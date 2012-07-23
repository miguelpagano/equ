{-# Language OverloadedStrings #-}
-- | Este modulo es el parser de pruebas.
module Equ.Parser.Proof ( parsePfFromString'
                        , rel 
                        , proof
                        , parseFromFileProof
                        , initPProofState
                        , PProofState
                        , pProofSet) where

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

import System.IO.Unsafe

type ProofName = Text
type HypName = Text

type ProofSet = M.Map ProofName (Maybe Proof)
type HypSet = M.Map HypName Hypothesis

data PProofState = PProofState { pHypSet :: HypSet
                               , pProofSet :: ProofSet
                               , pVarTy :: VarTy
                               , pUseParen :: ParenFlag
                               }

type ParserP a = ParsecT String PProofState Identity a

-- | Retorna la pila de teoremas declarados.
getProofSet :: ParserP ProofSet
getProofSet = pProofSet <$> getState

-- | Retorna la pila de teoremas declarados.
getHypSet :: ParserP HypSet
getHypSet = pHypSet <$> getState

-- | Parsea un final de prueba que comienza con begin proof.
parseProofEnd :: ParserP ()
parseProofEnd = many newline >> keywordEnd >> keywordProof

-- | Borra las hipotesis del estado del parser de pruebas.
resetHypSet :: ParserP ()
resetHypSet = do pst <- getState
                 putState $ pst {pHypSet = M.empty}

-- | Si el conjunto de pruebas declaradas es vacio.
proofSetIsEmpty :: ParserP Bool
proofSetIsEmpty = M.null <$> getProofSet

-- | Añade un nombre de declaración de prueba con su prueba si es que existe.                
addHypName :: HypName -> Hypothesis -> ParserP ()
addHypName hypname hyp = do
            pst <- getState
            let hypSet = pHypSet pst
            let pSet = pProofSet pst
            case (M.lookup hypname hypSet, M.lookup hypname pSet) of
                (_,Just _) -> fail $ show hypname ++ 
                                     " corresponde a un nombre de teorema."
                (Just _,_) -> fail $ "El nombre de hipótesis " ++ show hypname 
                                     ++ " ya ha sido utilizado."
                _ -> do let hypSetUpdated = M.insert hypname hyp hypSet
                        putState $ pst {pHypSet = hypSetUpdated}

-- | Hace un lookup de un teorema declarado antes en base a su nombre.
getDeclProof :: ProofName -> ParserP (Maybe Proof)
getDeclProof pn = do
                pst <- getState
                let proofSet = pProofSet pst
                case M.lookup pn proofSet of
                    (Just mproof) -> return mproof
                    _ -> return Nothing

-- | Añade un nombre de declaración de prueba con su prueba si es que existe.                
addProofNameWithProof :: ProofName -> Maybe Proof -> ParserP ()
addProofNameWithProof pn p = do
            pst <- getState
            let proofSet = pProofSet pst
            let hypSet = pHypSet pst
            case (M.lookup pn proofSet) of
                Just (Just _) -> fail $ "El nombre de teorema " ++ 
                                        show pn ++ " ya ha sido utilizado."
                _ -> do let proofSetUpdated = M.insert pn p proofSet
                        putState $ pst {pProofSet = proofSetUpdated}

lexer :: GenTokenParser String PProofState Identity
lexer = lexer' { whiteSpace = oneOf " \t" >> return ()}
    where
        lexer' :: TokenParser PProofState
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

whites :: ParserP ()
whites = whiteSpace lexer

keyword :: String -> ParserP ()
keyword  = reserved lexer
keywordBegin :: ParserP ()
keywordBegin = keyword "begin"
keywordBasic :: ParserP ()
keywordBasic = keyword "basic"
keywordExhaustive :: ParserP ()
keywordExhaustive = keyword "exhaustive"
keywordEnd :: ParserP ()
keywordEnd = keyword "end" >> resetHypSet
keywordSBOpen :: ParserP ()
keywordSBOpen = try $ symbol lexer "[" >> symbol lexer "~" >> return ()
keywordSBClose :: ParserP ()
keywordSBClose = try $ symbol lexer "~" >> symbol lexer "]" >> return ()
keywordDots :: ParserP ()
keywordDots = symbol lexer ":" >> return ()
keywordComma :: ParserP ()
keywordComma = symbol lexer "," >> return ()
keywordProof :: ParserP ()
keywordProof = keyword "proof"
keywordCases :: ParserP ()
keywordCases = keyword "cases"
keywordInduc :: ParserP ()
keywordInduc = keyword "induction"
keywordFor :: ParserP ()
keywordFor = keyword "for"
keywordIn :: ParserP ()
keywordIn = keyword "in"
keywordDot :: ParserP ()
keywordDot = keyword "."
keywordRArrow :: ParserP ()
keywordRArrow = keyword "->"
keywordWith :: ParserP ()
keywordWith = keyword "with"
keywordWhere :: ParserP ()
keywordWhere = keyword "where"

-- | Parsea nombres de declaración de teoremas.
parseProofName :: ParserP Text
parseProofName = parseName >>= \n -> addProofNameWithProof n Nothing >> return n

-- | Parsea nombres de declaración de hipotesis.
parseDeclHypName :: ParserP Text
parseDeclHypName = parseName' keywordDots

-- | Parsea nombres de hipotesis en el contexto de una justificación.
parseHypName :: ParserP Text
parseHypName = parseName

-- | Parsea nombres.
parseName :: ParserP Text
parseName =  parseName' (tryNewline <|> whites)

parseName' :: ParserP end -> ParserP Text
parseName' till = lexeme lexer (manyTill name till) >>= \s -> return (pack s)
    where
        name :: ParserP Char
        name = foldr (\s -> (<|>) (keyword s >> unexpected (show s))) letter rNames

tryNewline :: ParserP ()
tryNewline = newline >> return ()

-- | Parser de un axioma, con nombre de teoría.
axiomQual :: [TheoryName] -> ParserP Axiom
axiomQual ths = pTheory >>= \thy -> 
                if thy `elem` ths 
                then char '.' >> 
                    (choice . map axiomInList . fromJust . lookup thy) axiomGroup
                else parserZero
                
-- | Parser de un axioma sin tener en cuenta la teoría.
axiomUnQual :: [TheoryName] -> ParserP Axiom
axiomUnQual ths = (choice . map axiomInList . concatMap snd) axiomGroup

-- | Construcción del parser a partir del axioma.
axiomInList :: Axiom -> ParserP Axiom
axiomInList ax = try $ (string . unpack . axName) ax >> return ax

-- | Parser del nombre de una teoría; notar que el conjunto de teorías
-- conocidas está definido en 'Equ.Theories.theories'
pTheory :: ParserP TheoryName
pTheory = pack <$> choice (map (string . unpack) theories)

-- | Si el tipo 'a' tiene un campo 'Text', generamos un parser para
-- ese tipo. Esta es la versión lifteada a listas de 'a'.
anyText :: (a -> Text) -> [a] -> ParserP a
anyText f = choice . map el
    where el a = a <$ (try . string . unpack . f) a

-- | Parsea la declaración de una entidad.
declaration :: String -> ParserP String
declaration decl = string ("new " ++ decl  ++ " ")  >> spaces >>
                   concat <$> endBy (many (noneOf "\n")) newline

-- | Parser para la definición de un teorema; notar que no se
-- valida la prueba.
declTheorem :: ParserP Theorem
declTheorem = declaration "theorem" >>= \thName ->
              proof Nothing False >>= \thPrf -> 
              return (createTheorem (pack thName) thPrf)

-- | Parser para una lista de teoremas.
prelude :: ParserP [Theorem]
prelude = sepBy declTheorem (newline >> newline)

-- | Parser de una sesión. 
-- TODO: considerar que un teorema dependa de los teoremas 
-- previamente definidos; considerar declaración de hipótesis.
session :: ParserP ([Theorem],Ctx,Proof)
session = prelude >>= \ths ->          
          proof Nothing False >>= \prf ->
          return (ths,beginCtx,prf)

-- | Parser del uso de un teorema; notar que necesitamos la lista de 
-- teoremas conocidos en este momento.
theorem :: [Theorem] -> ParserP Theorem
theorem = anyText thName

-- | Uso del parser de una expresión definido en 'Equ.Parser.Expr'.
-- Ale: No esta bonito como manejamos el pasaje de errores con pass
-- ademas pasa que tenemos que re-acomodar la posición del error.
-- Algo raro es que la posición de la linea siempre esta un lugar mas "adelante"
parseFocus :: ParserP () -> ParserP Focus
parseFocus till = 
            getState >>= \st ->
            exprL (makePExprState st) <$> manyTill anyChar till >>= pass
    where
        pass :: Either ParseError Focus -> ParserP Focus
        pass ef = case ef of
                        Right e -> return e
                        Left per -> getPosition >>= \p -> 
                                    fail $ show $ flip setErrorPos per $
                                    setSourceLine (errorPos per) (sourceLine p-1)
        exprL' :: Parser' Focus
        exprL' = (toFocus . unParen) <$> (spaces >> parsePreExpr >>= 
                                         \expr -> eof >> return expr)
        exprL :: PExprState -> String -> Either ParseError Focus
        exprL st s = runParser exprL' st "" s
        makePExprState :: PProofState -> PExprState
        makePExprState st = PExprState (pVarTy st) (pUseParen st)
        

-- | Parser de una justificación inmediata de un paso de prueba.
-- TODO: considerar hipótesis.
basic :: ParserP Basic
basic =  Ax   <$> axiomUnQual theories
     <|> Theo <$> parseTheo
     <|> Hyp  <$> parseHyp
    where
        parseHyp :: ParserP Hypothesis
        parseHyp = try $ 
                    do
                    n <- parseHypName
                    hSet <- getHypSet
                    maybe (return $ dummyHypothesis n) return (M.lookup n hSet)
        parseTheo :: ParserP Theorem
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
braced :: ParserP a -> ParserP a
braced = between (string "{" >> spaces) (spaces >> string "}" )

-- | Parser de un paso de prueba.
justification :: ParserP (Relation, Maybe Basic)
justification = rel >>= \r -> spaces >>
                optionMaybe (braced basic) >>= \j -> 
                char '\n' >> return (r, j)

-- | Parsea todas las pruebas de un archivo y retorna una lista con estas mismas.
prooflist :: Maybe Ctx -> ParserP [Proof]
prooflist mc = many (proof mc True)

-- | Parser de declaraciones de hipótesis.
parseHypothesis :: ParserP [Hypothesis]
parseHypothesis = do
                    keywordSBOpen
                    many whites
                    hyps <- many $ try $ parseHyp keywordComma
                    hyp <- parseHyp keywordSBClose
                    return $ hyps ++ [hyp]
    where
        parseHyp :: ParserP () -> ParserP Hypothesis
        parseHyp till = do
                n <- parseDeclHypName
                f <- parseFocus till
                return $ createHypothesis n (Expr $ toExpr f) (GenConditions [])

dummyHypothesis ::Text -> Hypothesis
dummyHypothesis text = createHypothesis text dummyExpr (GenConditions [])
    where
        dummyExpr :: Expr
        dummyExpr = Expr $ BinOp (relToOp relEq) (preExprHole "") (preExprHole "")

-- | Parser de pruebas.
proof :: Maybe Ctx -> Bool -> ParserP Proof
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
        makeCtx :: Maybe [Hypothesis] -> ParserP Ctx
        makeCtx = maybe (return ctx) (return . foldr addHypothesis' ctx)
        
        parseProof :: ParserP Proof
        parseProof = 
            parsePrefix >>= \(mname,mhyps) -> many newline >>
            makeCtx mhyps >>= \ctxWithHyps ->
            choice [ inducProof ctxWithHyps
                   , casesProof ctxWithHyps
                   , transProof ctxWithHyps flag
                   ] >>= \p ->
            maybe (return p) (addProofNWP p) mname
        
        parsePrefix :: ParserP (Maybe Text,Maybe [Hypothesis])
        parsePrefix = 
            choice 
            [ try (newline >> return (Nothing,Nothing))
            , try (parseProofName >>= \n -> parseHypothesis >>= \hs -> 
                   mapM_ addHypsToState hs >>
                   return (Just n, Just hs))
            , try (parseProofName >>= \n -> return (Just n, Nothing))
            , try (parseHypothesis >>= \hs -> mapM_ addHypsToState hs >> 
                   return (Nothing, Just hs))
            , return (Nothing,Nothing)
            ]
        
        addProofNWP :: Proof -> ProofName -> ParserP Proof
        addProofNWP p name = addProofNameWithProof name (Just p) >> return p
        addHyps :: [Hypothesis] -> Ctx -> Ctx
        addHyps hyps ctx = foldr addHypothesis' ctx hyps
        addHypsToState :: Hypothesis -> ParserP ()
        addHypsToState hyp = addHypName (truthName hyp) hyp
        addHypsToProof :: Proof -> [Hypothesis] -> ParserP Proof
        addHypsToProof p hyps = do
                    let Just ctx = getCtx p
                    return $ fromJust $ setCtx (addHyps hyps ctx) p

-- | Parseo de una prueba inductiva.
inducProof :: Ctx -> ParserP Proof
inducProof ctx = do
            keywordInduc
            keywordIn
            fInduc <- parseFocus keywordFor
            fei <- parseFocus keywordDot
            [rel] <- manyTill rel keywordDot
            fef <- parseFocus keywordWhere
            let ex = toExpr fef
            --error $ "ex es = " ++ show ex
            typedFinduc <- typeVarInducM ex fInduc-- fInduc
            -- () <- return $ unsafePerformIO $ (putStrLn $ "--------EITHERF es :--------" ++ show eitherF)
            -- typedFinduc <- return $ fInduc  
            
            cs <- parseInducCases ctx rel fei fef (toExpr typedFinduc)
            parseProofEnd
            let p = Ind ctx rel fei fef typedFinduc cs
            return p 
    where
        makeExpr :: Relation -> Focus -> Focus -> PreExpr
        makeExpr r e e' = BinOp (relToOp r) (toExpr e) (toExpr e')
        typeVarInducM e (Var v,_) = either (error . show) (\t -> return . toFocus . Var $ v { varTy = t }) $ checkPreExpr e
        typeVarInduc :: PreExpr -> Focus -> Either ProofError Focus
        typeVarInduc e (Var fInduc,_) = do
            typedFei <- either (Left . (flip ProofError id)
                                     . ClashTypingProofExpr . fst)
                               return 
                               (typeCheckPreExpr e)
            let xs = (Set.toList $ freeVars typedFei)
            maybe (Left $ ProofError (InductionError VarIndNotInExpr) id) 
                  (return . toFocus . Var)
                  (find (==fInduc) (Set.toList (freeVars typedFei)))
        parseInducCases:: Ctx -> Relation -> Focus -> Focus -> PreExpr -> 
                          ParserP [(Focus,Proof)]
        parseInducCases ctx r fei fef (Var indv) = do
                    keywordBasic
                    c <- parseCases ctx indv
                    cs <- manyTill (parseCases ctx indv) (many newline >> keywordInduc)
                    patt <- parseFocus keywordWith
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
casesProof :: Ctx -> ParserP Proof
casesProof ctx = do
        keywordCases
        keywordIn
        fc <- parseFocus keywordFor
        fei <- parseFocus keywordDot
        [rel] <- manyTill rel keywordDot
        fef <- parseFocus keywordWhere
        (cs, mPEx) <- manyTillWithEnd (parseCases ctx undefined) (endExhaustive <|> endProof)
        let cs' = map (\ p -> (fst p, fromJust $ addHypothesisCase p)) cs
        return (Cases ctx rel fei fef fc cs' mPEx)
    where
        endExhaustive :: ParserP (Maybe Proof)
        endExhaustive = do
                        pExh <- parseExhaustive
                        parseProofEnd
                        return $ Just pExh
        endProof :: ParserP (Maybe Proof)
        endProof = parseProofEnd >> return Nothing
        parseExhaustive :: ParserP Proof
        parseExhaustive = keywordExhaustive >> keywordRArrow >>
                          proof (Just beginCtx) False
        manyTillWithEnd :: (Stream s m t) => ParsecT s u m a -> 
                            ParsecT s u m end -> ParsecT s u m ([a],end)
        manyTillWithEnd p end = scan
            where
                scan =  do{ e <- end; return ([], e) }
                    <|> do{ x <- p; xs <- scan; return (x:fst xs,snd xs)}
                    
        addHypothesisCase :: (Focus,Proof) -> Maybe Proof
        addHypothesisCase (f,p) =
            let hyp = createHypothesis "Caso" (Expr $ toExpr f) (GenConditions []) in
                getCtx p >>= \ctx ->
                setCtx (addHypothesis' hyp ctx) p
                    

-- -- | Parsea casos, de la forma expr -> transProof
parseCases :: Ctx -> Variable -> ParserP (Focus, Proof)
parseCases ctx v = do
            fi <- parseFocus keywordRArrow
            ctx' <- return $ instanciateInCtx ctx v fi
            p <- proof (Just ctx) False
            return (fi,p)
            
-- | Parser de pruebas transitivas, estan incluidas las pruebas simples.
transProof :: Ctx -> Bool -> ParserP Proof
transProof ctx flag = do
                      e1 <- parseFocus tryNewline
                      pSet <- getProofSet
                      mkTrans ctx e1 pSet <$> manyExprLine
    where
        parseStep :: ParserP (Focus,(Relation, Maybe Basic))
        parseStep = do
                    rj <- justification
                    e <- parseFocus tryNewline
                    return (e,rj)

        manyExprLine :: ParserP [(Focus,(Relation, Maybe Basic))]
        manyExprLine = do 
                        frb <- parseStep
                        frbs <- if flag 
                               then manyTill parseStep parseProofEnd
                               else many parseStep
                        return (frb:frbs)

-- | Parser de la relación sobre la que estamos haciendo la prueba.
rel :: ParserP Relation
rel = foldr ((<|>) . uncurry prel) parserZero relations
    where prel iden ty = ty <$ try (many whites >> string iden)
          relations = [("=",relEq), ("≡",relEquiv), ("⇒",relImpl), ("⇐",relCons)]

-- | Parser de prueba.
parsePfFromString' :: String -> Either ParseError [Proof]
parsePfFromString' = either handleError Right . runParser 
                            (prooflist Nothing) (initPProofState UnusedParen) ""
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
initPProofState :: ParenFlag -> PProofState
initPProofState = PProofState M.empty M.empty initVarTy
    where
        initVarTy :: VarTy
        initVarTy = (0,M.empty)

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
