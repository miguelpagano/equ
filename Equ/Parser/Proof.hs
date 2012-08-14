{-# Language OverloadedStrings #-}
-- | Este modulo es el parser de pruebas.
module Equ.Parser.Proof {-( parsePfFromString'
                        , rel 
                        , proof
                        , parseFromFileProof
                        , initPProofState
                        , PProofState
                        , pProofSet) -}where

import Equ.Parser.Expr
import Equ.Syntax hiding (Hole)
import Equ.Expr (Expr(..))
import Equ.PreExpr ( PreExpr'(..),PreExpr,toFocus, preExprHole
                   , Focus,unParen,toExpr, freeVars,applySubst)
import Equ.TypeChecker (typeCheckPreExpr,checkPreExpr)
import Equ.Proof ( validateProof, printProof
                 , holeProof, newProofWithCases, newProof
                 , validateProof)
import Equ.Proof.Error(errProof, ProofError(..), ProofError'(..)
                      , PErrorInduction(VarIndNotInExpr))
import Equ.Proof.Proof ( Proof'(..)
                       , Ctx
                       , Basic (..) 
                       , Theorem (..)
                       , Axiom (..)
                       , Truth (..)
                       , Hypothesis (..)
                       , getEnd 
                       , getStart
                       , beginCtx
                       , addHypothesis'
                       , getCtx
                       , setCtx
                       , Proof
                       , instanciateInCtx)
import Equ.Proof.Condition
import Equ.Proof.Induction (createIndHypothesis)
import Equ.Theories (theories,axiomGroup,TheoryName, relToOp
                    ,createTheorem,theoremAddProof, createHypothesis)
import Equ.Rule hiding (rel)

import Text.Parsec
import Text.Parsec.Error(setErrorPos)
import Text.Parsec.Token
import Text.Parsec.Language
import Text.Parsec.String
import Text.Parsec.Combinator
import qualified Text.Parsec.Expr as PE

import Data.Text(Text,pack,unpack)
import qualified Data.Set as Set (toList)
import Data.Maybe
import Data.Either(partitionEithers)
import Data.List (intersperse, find)
import qualified Data.Map as M (Map,empty,insert,toList,null, lookup, map,singleton) 

import Control.Monad.Identity
import Control.Applicative ((<$>),(<$),(<*>))

type ProofName = Text
type HypName = Text

type ProofSet = M.Map ProofName (Maybe Proof)
type HypSet = M.Map HypName Hypothesis

data PProofState = PProofState { pHypSet :: HypSet
                               , pProofSet :: ProofSet
                               , pExprSt :: PExprState
                               }

class PProofStateClass a where
    pProofState :: a -> PProofState
    setProofState :: a -> PProofState -> a

instance PExprStateClass PProofState where
    pExprState = pExprSt

instance PProofStateClass PProofState where
    pProofState = id
    setProofState state pst = pst

type ParserP a b = ParsecT String a Identity b

-- | Retorna la pila de teoremas declarados.
getProofSet :: (PExprStateClass s, PProofStateClass s) => ParserP s ProofSet
getProofSet = pProofSet . pProofState <$> getState

-- | Retorna la pila de teoremas declarados.
getHypSet :: (PExprStateClass s, PProofStateClass s) => ParserP s HypSet
getHypSet = pHypSet . pProofState <$> getState

-- | Parsea un final de prueba que comienza con begin proof.
parseProofEnd :: (PExprStateClass s, PProofStateClass s) => ParserP s ()
parseProofEnd = many newline >> keywordEnd >> keywordProof

-- | Borra las hipotesis del estado del parser de pruebas.
resetHypSet :: (PExprStateClass s, PProofStateClass s) => ParserP s ()
resetHypSet = do pst <- getState
                 let pst' = pProofState pst
                 putState $ setProofState pst $ pst' {pHypSet = M.empty}


-- | Si el conjunto de pruebas declaradas es vacio.
proofSetIsEmpty :: (PExprStateClass s, PProofStateClass s) => ParserP s Bool
proofSetIsEmpty = M.null <$> getProofSet

-- | Añade un nombre de declaración de prueba con su prueba si es que existe.                
addHypName :: (PExprStateClass s, PProofStateClass s) => 
              HypName -> Hypothesis -> ParserP s ()
addHypName hypname hyp = do
            pst' <- getState
            let pst = pProofState pst'
            let hypSet = pHypSet pst
            let pSet = pProofSet pst
            case (M.lookup hypname hypSet, M.lookup hypname pSet) of
                (_,Just _) -> fail $ show hypname ++ 
                                     " corresponde a un nombre de teorema."
                (Just _,_) -> fail $ "El nombre de hipótesis " ++ show hypname 
                                     ++ " ya ha sido utilizado."
                _ -> do let hypSetUpdated = M.insert hypname hyp hypSet
                        --putState $ pst' {pHypSet = hypSetUpdated}
                        return ()

-- | Hace un lookup de un teorema declarado antes en base a su nombre.
getDeclProof :: (PExprStateClass s, PProofStateClass s) => 
                ProofName -> ParserP s (Maybe Proof)
getDeclProof pn = do
                pst' <- getState
                let pst = pProofState pst'
                let proofSet = pProofSet pst
                case M.lookup pn proofSet of
                    (Just mproof) -> return mproof
                    _ -> return Nothing

-- | Añade un nombre de declaración de prueba con su prueba si es que existe.                
addProofNameWithProof :: (PExprStateClass s, PProofStateClass s) => 
                         ProofName -> Maybe Proof -> ParserP s ()
addProofNameWithProof pn p = do
            pst' <- getState
            let pst = pProofState pst'
            let proofSet = pProofSet pst
            let hypSet = pHypSet pst
            case (M.lookup pn proofSet) of
                Just (Just _) -> fail $ "El nombre de teorema " ++ 
                                        show pn ++ " ya ha sido utilizado."
                _ -> do let proofSetUpdated = M.insert pn p proofSet
                        return ()
--                        putState $ pst' {pProofSet = proofSetUpdated}

lexer :: (PExprStateClass s, PProofStateClass s) =>
         GenTokenParser String s Identity
lexer = lexer' { whiteSpace = oneOf " \t" >> return ()}
    where
        lexer' :: (PExprStateClass s, PProofStateClass s) => TokenParser s
        lexer' = makeTokenParser $ 
                    emptyDef { reservedNames = rNames
                             , identStart  = alphaNum <|> char '_'
                             , identLetter = alphaNum <|> char '_'
                             , caseSensitive = False
                             }

-- | Nombres reservados.
rNames :: [String]
rNames = [ "proof"
         , "with"
         , "for"
         , "cases"
         , "->"
         , "where"
         , "induction"
         , "in"
         , "begin"
         , "end"
         , "basic"
         , "exhaustive"
         ]

whites :: (PExprStateClass s, PProofStateClass s) => ParserP s ()
whites = whiteSpace lexer

keyword :: (PExprStateClass s, PProofStateClass s) => String -> ParserP s ()
keyword  = reserved lexer
keywordBegin :: (PExprStateClass s, PProofStateClass s) => ParserP s ()
keywordBegin = keyword "begin"
keywordBasic :: (PExprStateClass s, PProofStateClass s) => ParserP s ()
keywordBasic = keyword "basic"
keywordExhaustive :: (PExprStateClass s, PProofStateClass s) => ParserP s ()
keywordExhaustive = keyword "exhaustive"
keywordEnd :: (PExprStateClass s, PProofStateClass s) => ParserP s ()
keywordEnd = keyword "end" >> resetHypSet
keywordSBOpen :: (PExprStateClass s, PProofStateClass s) => ParserP s ()
keywordSBOpen = try (symbol lexer "[") >> symbol lexer "~" >> return ()
keywordSBClose :: (PExprStateClass s, PProofStateClass s) => ParserP s ()
keywordSBClose = try (symbol lexer "~") >> symbol lexer "]" >> return ()
keywordDots :: (PExprStateClass s, PProofStateClass s) => ParserP s ()
keywordDots = symbol lexer ":" >> return ()
keywordComma :: (PExprStateClass s, PProofStateClass s) => ParserP s ()
keywordComma = symbol lexer "," >> return ()
keywordProof :: (PExprStateClass s, PProofStateClass s) => ParserP s ()
keywordProof = keyword "proof"
keywordCases :: (PExprStateClass s, PProofStateClass s) => ParserP s ()
keywordCases = keyword "cases"
keywordInduc :: (PExprStateClass s, PProofStateClass s) => ParserP s ()
keywordInduc = keyword "induction"
keywordFor :: (PExprStateClass s, PProofStateClass s) => ParserP s ()
keywordFor = keyword "for"
keywordIn :: (PExprStateClass s, PProofStateClass s) => ParserP s ()
keywordIn = keyword "in"
keywordDot :: (PExprStateClass s, PProofStateClass s) => ParserP s ()
keywordDot = keyword "."
keywordRArrow :: (PExprStateClass s, PProofStateClass s) => ParserP s ()
keywordRArrow = keyword "->"
keywordWith :: (PExprStateClass s, PProofStateClass s) => ParserP s ()
keywordWith = keyword "with"
keywordWhere :: (PExprStateClass s, PProofStateClass s) => ParserP s ()
keywordWhere = keyword "where"

-- | Parsea nombres de declaración de teoremas.
parseProofName :: (PExprStateClass s, PProofStateClass s) => ParserP s Text
parseProofName = parseName >>= \n -> addProofNameWithProof n Nothing >> return n

-- | Parsea nombres de declaración de hipotesis.
parseDeclHypName :: (PExprStateClass s, PProofStateClass s) => ParserP s Text
parseDeclHypName = parseName' keywordDots

-- | Parsea nombres de hipotesis en el contexto de una justificación.
parseHypName :: (PExprStateClass s, PProofStateClass s) => ParserP s Text
parseHypName = parseName

-- | Parsea nombres.
parseName :: (PExprStateClass s, PProofStateClass s) => ParserP s Text
parseName =  parseName' (tryNewline <|> whites)

parseName' :: (PExprStateClass s, PProofStateClass s) => ParserP s end -> ParserP s Text
parseName' till = lexeme lexer (manyTill name till) >>= \str -> return (pack str)
    where
        name :: (PExprStateClass s, PProofStateClass s) => ParserP s Char
        name = foldr (\str -> (<|>) (keyword str >> unexpected (show str))) letter rNames

tryNewline :: (PExprStateClass s, PProofStateClass s) => ParserP s ()
tryNewline = newline >> return ()

-- | Parser de un axioma, con nombre de teoría.
axiomQual :: (PExprStateClass s, PProofStateClass s) => [TheoryName] -> ParserP s Axiom
axiomQual ths = pTheory >>= \thy -> 
                if thy `elem` ths 
                then char '.' >> 
                    (choice . map axiomInList . fromJust . lookup thy) axiomGroup
                else parserZero
                
-- | Parser de un axioma sin tener en cuenta la teoría.
axiomUnQual :: (PExprStateClass s, PProofStateClass s) => [TheoryName] -> ParserP s Axiom
axiomUnQual ths = (choice . map axiomInList . concatMap snd) axiomGroup

-- | Construcción del parser a partir del axioma.
axiomInList :: (PExprStateClass s, PProofStateClass s) => Axiom -> ParserP s Axiom
axiomInList ax = try $ (string . unpack . axName) ax >> return ax

-- | Parser del nombre de una teoría; notar que el conjunto de teorías
-- conocidas está definido en 'Equ.Theories.theories'
pTheory :: (PExprStateClass s, PProofStateClass s) => ParserP s TheoryName
pTheory = pack <$> choice (map (string . unpack) theories)

-- | Si el tipo 'a' tiene un campo 'Text', generamos un parser para
-- ese tipo. Esta es la versión lifteada a listas de 'a'.
anyText :: (PExprStateClass s, PProofStateClass s) => (a -> Text) -> [a] -> ParserP s a
anyText f = choice . map el
    where el a = a <$ (try . string . unpack . f) a

-- | Parsea la declaración de una entidad.
declaration :: (PExprStateClass s, PProofStateClass s) => String -> ParserP s String
declaration decl = string ("new " ++ decl  ++ " ")  >> spaces >>
                   concat <$> endBy (many (noneOf "\n")) newline

-- | Parser para la definición de un teorema; notar que no se
-- valida la prueba.
declTheorem :: (PExprStateClass s, PProofStateClass s) => ParserP s Theorem
declTheorem = declaration "theorem" >>= \thName ->
              proof Nothing False >>= \thPrf -> 
              return (createTheorem (pack thName) thPrf)

-- | Parser para una lista de teoremas.
prelude :: (PExprStateClass s, PProofStateClass s) => ParserP s [Theorem]
prelude = sepBy declTheorem (newline >> newline)

-- | Parser de una sesión. 
-- TODO: considerar que un teorema dependa de los teoremas 
-- previamente definidos; considerar declaración de hipótesis.
session :: (PExprStateClass s, PProofStateClass s) => ParserP s ([Theorem],Ctx,Proof)
session = prelude >>= \ths ->          
          proof Nothing False >>= \prf ->
          return (ths,beginCtx,prf)

-- | Parser del uso de un teorema; notar que necesitamos la lista de 
-- teoremas conocidos en este momento.
theorem :: (PExprStateClass s, PProofStateClass s) => [Theorem] -> ParserP s Theorem
theorem = anyText thName

-- | Uso del parser de una expresión definido en 'Equ.Parser.Expr'.
-- Ale: No esta bonito como manejamos el pasaje de errores con pass
-- ademas pasa que tenemos que re-acomodar la posición del error.
-- Algo raro es que la posición de la linea siempre esta un lugar mas "adelante"
parseFocus :: (PExprStateClass s, PProofStateClass s) => ParserP s Focus
parseFocus = parsePreExpr >>= return . toFocus
--             getState >>= \st ->
--             exprL (makePExprState st) <$> manyTill anyChar till >>= pass
--     where
--         pass :: Either ParseError Focus -> ParserP Focus
--         pass ef = case ef of
--                         Right e -> return e
--                         Left per -> getPosition >>= \p -> 
--                                     fail $ show $ flip setErrorPos per $
--                                     setSourceLine (errorPos per) (sourceLine p-1)
--         exprL' :: Parser' Focus
--         exprL' = (toFocus . unParen) <$> (spaces >> parsePreExpr >>= 
--                                          \expr -> eof >> return expr)
--         exprL :: PExprState -> String -> Either ParseError Focus
--         exprL st s = runParser exprL' st "" s
--         makePExprState :: PProofState -> PExprState
--         makePExprState st = PExprState $ pUseParen st
        

-- | Parser de una justificación inmediata de un paso de prueba.
-- TODO: considerar hipótesis.
basic :: (PExprStateClass s, PProofStateClass s) => ParserP s Basic
basic =  Ax   <$> axiomUnQual theories
     <|> Theo <$> parseTheo
     <|> Hyp  <$> parseHyp
    where
        parseHyp :: (PExprStateClass s, PProofStateClass s) => ParserP s Hypothesis
        parseHyp = try $ 
                    do
                    n <- parseHypName
                    hSet <- getHypSet
                    maybe (return $ dummyHypothesis n) return (M.lookup n hSet)
        parseTheo :: (PExprStateClass s, PProofStateClass s) => ParserP s Theorem
        parseTheo = try $
                    do
                    n <- parseProofName
                    mp <- getDeclProof n
                    maybe (fail $ theoErr n) (return . createTheorem n) mp
        theoErr :: ProofName -> String
        theoErr n = "Prueba del teorema: " ++ show (unpack n)
        hypErr :: HypName -> String
        hypErr n = "Declaración de la hipótesis: " ++ show (unpack n)

-- | Parser de entidades entre llaves.
braced :: (PExprStateClass s, PProofStateClass s) => ParserP s a -> ParserP s a
braced = between (string "{" >> spaces) (spaces >> string "}" )

-- | Parser de un paso de prueba.
justification :: (PExprStateClass s, PProofStateClass s) => ParserP s (Relation, Maybe Basic)
justification = rel >>= \r -> spaces >>
                optionMaybe (braced basic) >>= \j -> 
                return (r, j)

-- | Parsea todas las pruebas de un archivo y retorna una lista con estas mismas.
prooflist :: (PExprStateClass s, PProofStateClass s) => Maybe Ctx -> ParserP s [Proof]
prooflist mc = many (proof mc True)

-- | Parser de declaraciones de hipótesis.
parseHypothesis :: (PExprStateClass s, PProofStateClass s) => ParserP s [Hypothesis]
parseHypothesis = do
                    keywordSBOpen
                    many whites
                    hyps <- many $ try $ parseHyp keywordComma
                    hyp <- parseHyp keywordSBClose
                    return $ hyps ++ [hyp]
    where
        parseHyp :: (PExprStateClass s, PProofStateClass s) =>
                    ParserP s () -> ParserP s Hypothesis
        parseHyp till = do
                n <- parseDeclHypName
                f <- parseFocus
                till
                return $ createHypothesis n (Expr $ toExpr f) (GenConditions [])

dummyHypothesis ::Text -> Hypothesis
dummyHypothesis text = createHypothesis text dummyExpr (GenConditions [])
    where
        dummyExpr :: Expr
        dummyExpr = Expr $ BinOp (relToOp relEq) (preExprHole "") (preExprHole "")

-- | Parser de pruebas.
proof :: (PExprStateClass s, PProofStateClass s) => Maybe Ctx -> 
         Bool -> ParserP s Proof
proof mc flag = do
        many newline
        when flag keywordBegin
        -- Acá no queremos usar keywordProof para mantener el "\n".
        -- Medio en resumen, lo necesitamos para el primer caso del choice
        -- si no estuviera, entra directo a parseProofName.
        when flag (string "proof" >> many whites >> return ())
        if flag then parseProof else transProof ctx flag
    where
        ctx :: Ctx
        ctx = fromMaybe beginCtx mc
        makeCtx :: (PExprStateClass s, PProofStateClass s) =>
                   Maybe [Hypothesis] -> ParserP s Ctx
        makeCtx = maybe (return ctx) (return . foldr addHypothesis' ctx)
        
        parseProof :: (PExprStateClass s, PProofStateClass s) => ParserP s Proof
        parseProof = 
            parsePrefix >>= \(mname,mhyps) -> many newline >>
            makeCtx mhyps >>= \ctxWithHyps ->
            choice [ inducProof ctxWithHyps
                   , casesProof ctxWithHyps
                   , transProof ctxWithHyps flag
                   ] >>= \p ->
            maybe (return p) (addProofNWP p) mname
        
        parsePrefix :: (PExprStateClass s, PProofStateClass s) =>
                        ParserP s (Maybe Text,Maybe [Hypothesis])
        parsePrefix = 
            choice 
            [ try ((many1 newline) >> return (Nothing,Nothing))
            , try (parseProofName >>= \n -> parseHypothesis >>= \hs -> 
                   mapM_ addHypsToState hs >>
                   return (Just n, Just hs))
            , try (parseProofName >>= \n -> return (Just n, Nothing))
            , try (parseHypothesis >>= \hs -> mapM_ addHypsToState hs >> 
                   return (Nothing, Just hs))
            , return (Nothing,Nothing)
            ]
        
        addProofNWP :: (PExprStateClass s, PProofStateClass s) =>
                       Proof -> ProofName -> ParserP s Proof
        addProofNWP p name = addProofNameWithProof name (Just p) >> return p
        addHyps :: [Hypothesis] -> Ctx -> Ctx
        addHyps hyps ctx = foldr addHypothesis' ctx hyps
        addHypsToState :: (PExprStateClass s, PProofStateClass s) =>
                          Hypothesis -> ParserP s ()
        addHypsToState hyp = addHypName (truthName hyp) hyp
        addHypsToProof :: (PExprStateClass s, PProofStateClass s) =>
                          Proof -> [Hypothesis] -> ParserP s Proof
        addHypsToProof p hyps = do
                    let Just ctx = getCtx p
                    return $ fromJust $ setCtx (addHyps hyps ctx) p

-- | Parseo de una prueba inductiva.
inducProof :: (PExprStateClass s, PProofStateClass s) => Ctx -> ParserP s Proof
inducProof ctx = do
            keywordInduc
            keywordIn
            fInduc <- parseFocus
            keywordFor
            fei <- parseFocus
            keywordDot
            [rel] <- manyTill rel keywordDot
            fef <- parseFocus
            keywordWhere
            cs <- parseInducCases ctx rel fei fef (toExpr fInduc)
            parseProofEnd
            return $ Ind ctx rel fei fef fInduc cs
    where
        parseInducCases:: (PExprStateClass s, PProofStateClass s) => Ctx -> 
                          Relation -> Focus -> Focus -> 
                          PreExpr -> ParserP s [(Focus,Proof)]
        parseInducCases ctx r fei fef (Var indv) = do
                    keywordBasic
                    c <- parseCases ctx indv
                    cs <- manyTill (parseCases ctx indv) (many newline >> keywordInduc)
                    patt <- parseFocus
                    keywordWith
                    name <- parseName
                    let Just hypInd = createIndHypothesis r fei fef patt indv name
                    addHypName name hypInd
                    keywordRArrow
                    p <- proof (Just $ addHypothesis' hypInd ctx) False
                    return ((c:cs) ++ [(patt,p)])
        parseInducCases ctx r fei fef _ = undefined

-- | Parseo de una prueba por casos.
-- TODO: Es igual a la de arriba, pero esto tal vez vaya a cambiar, así que 
-- espero para acomodarla.
casesProof :: (PExprStateClass s, PProofStateClass s) => Ctx -> ParserP s Proof
casesProof ctx = do
        keywordCases
        keywordIn
        fc <- parseFocus
        keywordFor
        fei <- parseFocus
        keywordDot
        [rel] <- manyTill rel keywordDot
        fef <- parseFocus
        keywordWhere
        (cs, mPEx) <- manyTillWithEnd (parseCases ctx undefined) (endExhaustive <|> endProof)
        let cs' = map (\ p -> (fst p, fromJust $ addHypothesisCase p)) cs
        return (Cases ctx rel fei fef fc cs' mPEx)
    where
        endExhaustive :: (PExprStateClass s, PProofStateClass s) => ParserP s (Maybe Proof)
        endExhaustive = do
                        pExh <- parseExhaustive
                        parseProofEnd
                        return $ Just pExh
        endProof :: (PExprStateClass s, PProofStateClass s) => ParserP s (Maybe Proof)
        endProof = parseProofEnd >> return Nothing
        parseExhaustive :: (PExprStateClass s, PProofStateClass s) => ParserP s Proof
        parseExhaustive = keywordExhaustive >> keywordRArrow >>
                          proof (Just beginCtx) False
        addHypothesisCase :: (Focus,Proof) -> Maybe Proof
        addHypothesisCase (f,p) =
            let hyp = createHypothesis "Caso" (Expr $ toExpr f) (GenConditions []) in
                getCtx p >>= \ctx ->
                setCtx (addHypothesis' hyp ctx) p
                    
manyTillWithEnd :: (Stream s m t) => ParsecT s u m a -> 
                    ParsecT s u m end -> ParsecT s u m ([a],end)
manyTillWithEnd p end = scan
    where
        scan =  do{ e <- end; return ([], e) }
            <|> do{ x <- p; xs <- scan; return (x:fst xs,snd xs)}

-- -- | Parsea casos, de la forma expr -> transProof
parseCases :: Ctx -> Variable -> (PExprStateClass s, PProofStateClass s) => ParserP s (Focus, Proof)
parseCases ctx v = do
            fi <- parseFocus
            keywordRArrow
            ctx' <- return $ instanciateInCtx ctx v fi
            p <- proof (Just ctx) False
            return (fi,p)
            
-- | Parser de pruebas transitivas, estan incluidas las pruebas simples.
transProof :: Ctx -> Bool -> (PExprStateClass s, PProofStateClass s) => ParserP s Proof
transProof ctx flag = do
                      many whites
                      e1 <- parseFocus 
                      pSet <- getProofSet
                      mkTrans ctx e1 pSet <$> manyExprLine
    where
        parseStep :: (PExprStateClass s, PProofStateClass s) => ParserP s (Focus,(Relation, Maybe Basic))
        parseStep = do
                    --string "~"
                    rj <- justification
                    many (whites <|> tryNewline)
                    e <- parseFocus
                    return (e,rj)
        manyExprLine :: (PExprStateClass s, PProofStateClass s) => ParserP s [(Focus,(Relation, Maybe Basic))]
        manyExprLine = do 
                        frb <- parseStep
                        frbs <- if flag
                               then manyTill parseStep parseProofEnd
                               else many parseStep
                        return (frb:frbs)

-- | Parser de la relación sobre la que estamos haciendo la prueba.
rel :: (PExprStateClass s, PProofStateClass s) => ParserP s Relation
rel = foldr ((<|>) . uncurry prel) parserZero relations
    where prel iden ty = ty <$ try (many whites >> string iden)
          relations = [("=",relEq), ("≡",relEquiv), ("⇒",relImpl), ("⇐",relCons)]

-- | Parser de prueba.
parsePfFromString' :: String -> Either ParseError [Proof]
parsePfFromString' = either handleError Right . runParser 
                            (prooflist Nothing) (initPProofState $ initPExprState UnusedParen) ""
    where
        -- Esto esta pensando en que hay que hacer algo para obtener bien
        -- la posición del error.
        handleError :: ParseError -> Either ParseError [Proof]
        handleError = Left 

-- | Parsea una prueba desde un archivo.
parseFromFileProof :: FilePath -> IO ()
parseFromFileProof fp = readFile fp >>= \s -> 
                        case parsePfFromString' s of
                            Right ps -> print "-------" >> 
                                        print ps >> 
                                        print "-------" >> 
                                        print (map validateProof ps)
                            Left err -> print err

-- | Estado inicial del parser de pruebas.
initPProofState :: PExprState -> PProofState
initPProofState = PProofState M.empty M.empty

{- Pasar estas funciones a Equ.Proof -}
-- | construcción de una prueba simple.
mkSimple :: Ctx -> Relation -> Focus -> Focus -> Maybe Basic -> Proof
mkSimple c r e e' = maybe (Hole c r e e') (Simple c r e e')

-- | Construcción de una prueba transitiva; estas pruebas son
-- up-leaning, en el sentido que construyen pruebas donde el último
-- paso es simple mientras que todos los demás son transitivos.
mkTrans :: Ctx -> Focus -> ProofSet -> [(Focus,(Relation, Maybe Basic))] -> Proof
mkTrans c e pSet [] = error "impossible"
mkTrans c e pSet ((e',(r,j)):[]) = mkSimple c r e e' j
mkTrans c e pSet ((e',(r,j)):steps) = go (mkSimple c r e e' j) steps
    where 
        go :: Proof -> [(Focus,(Relation, Maybe Basic))] -> Proof
        go p [] = p
        go p ((e,(r, j)):ps) = go prf' ps
            where 
                e0 = fromJust (getStart p)
                e1 = fromJust (getEnd p)
                prf' = Trans c r e0 e1 e p (mkSimple c r e1 e j)
