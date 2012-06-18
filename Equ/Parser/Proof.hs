{-# Language RankNTypes #-}
-- | Este modulo es el parser de pruebas.
module Equ.Parser.Proof (parsePfFromString',rel,proof) where

import Equ.Parser.Expr
import Equ.PreExpr (PreExpr,toFocus,Focus,unParen)
import Equ.Proof (validateProof, printProof, holeProof)
import Equ.Proof.Proof ( Proof'(..)
                       , Ctx
                       , Basic (..) 
                       , Theorem (..)
                       , Axiom (..)
                       , Truth (..)
                       , getEnd 
                       , getStart
                       , beginCtx
                       , Proof)
import Equ.Theories (theories,axiomGroup,TheoryName,createTheorem,theoremAddProof)
import Equ.Rule hiding (rel)

import Data.Text(Text,pack,unpack)
import Text.Parsec
import Text.Parsec.Error(setErrorPos)
import Text.Parsec.Token
import Text.Parsec.Language
import Text.Parsec.String
import Text.Parsec.Combinator
import qualified Text.Parsec.Expr as PE

import Data.Maybe
import Data.Either(partitionEithers)
import Data.List (intersperse)
import qualified Data.Map as M (Map,empty,insert,toList,null, lookup) 

import Control.Monad.Identity
import Control.Applicative ((<$>),(<$),(<*>))

type ProofName = Text

type ProofSet = M.Map ProofName (Maybe Proof)

data PState = PState { pProofSet :: ProofSet
                     , pVarTy :: VarTy
                     }

type ParserP a = ParsecT String PState Identity a

-- | Retorna la pila de teoremas declarados.
getProofSet :: ParserP ProofSet
getProofSet = fmap pProofSet getState

-- | Parsea un final de prueba que comienza con begin proof.
parseProofEnd :: ParserP ()
parseProofEnd = many newline >> keywordEnd >> keywordProof

-- | Si el conjunto de pruebas declaradas es vacio.
proofSetIsEmpty :: ParserP Bool
proofSetIsEmpty = getProofSet >>= return . M.null

-- | Añade un nombre de declaración de prueba con su prueba si es que existe.                
addProofNameWithProof :: ProofName -> Maybe Proof -> ParserP ()
addProofNameWithProof pn p = do
                pst <- getState
                let proofSet = pProofSet pst
                case M.lookup pn proofSet of
                    (Just (Just _)) -> return () -- error al usar un mismo nombre para dos pruebas?
                    _ -> do let proofSetUpdated = M.insert pn p proofSet
                            putState $ pst {pProofSet = proofSetUpdated}

lexer :: GenTokenParser String PState Identity
lexer = lexer' { whiteSpace = oneOf " \t" >> return ()}
    where
        lexer' :: TokenParser PState
        lexer' = makeTokenParser $ 
                    emptyDef { reservedNames = rNames
                             , identStart  = alphaNum <|> char '_'
                             , identLetter = alphaNum <|> char '_'
                             , caseSensitive = False
                             }

-- | Nombres reservados.
rNames :: [String]
rNames = [ "proof", "with", "for", "cases", "->"
         , "where", "induction", "in", "begin"]

whites :: ParserP ()
whites = whiteSpace lexer

keyword :: String -> ParserP ()
keyword  = reserved lexer
keywordBegin :: ParserP ()
keywordBegin = keyword "begin"
keywordEnd :: ParserP ()
keywordEnd = keyword "end"
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
parseProofName =  
    fmap pack (lexeme lexer (manyTill name ((newline >> return ()) <|> whites)))
    where
        name :: ParserP Char
        name = letter

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
pTheory = fmap pack (choice (map (string . unpack) theories))

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
parseFocus till = getState >>= \st ->
                     fmap (exprL $ pVarTy st) (manyTill anyChar till) >>= pass
    where
        pass :: Either ParseError Focus -> ParserP Focus
        pass ef = case ef of
                        Right e -> return e
                        Left per -> getPosition >>= \p -> 
                                    fail $ show $ flip setErrorPos per $
                                    setSourceLine (errorPos per) (sourceLine p-1)
        exprL' :: Parser' Focus
        exprL' = fmap (toFocus . unParen) (spaces >> parsePreExpr)
        exprL :: VarTy -> String -> Either ParseError Focus
        exprL vt = runParser exprL' vt ""
        

-- | Parser de una justificación inmediata de un paso de prueba.
-- TODO: considerar hipótesis.
basic :: ParserP Basic
basic =  fmap Ax (axiomUnQual theories) 
     <|> fmap Theo (theorem [])
     <|> fmap (Theo . flip createTheorem (holeProof Nothing relEq)) (parseTheo)
    where
        parseTheo = parseTheoCase <|> parseTheoInduc <|> parseTheoTrans
        parseTheoTrans = do
                    keywordProof
                    keywordFor
                    fei <- parseFocus keywordDot
                    [rel] <- manyTill rel keywordDot
                    fef <- parseFocus keywordWith
                    n <- parseProofName
                    addProofNameWithProof n Nothing
                    return n
        parseTheoInduc = do
                    keywordInduc
                    parseTheoInducCases
        parseTheoCase = do
                    keywordCases
                    parseTheoInducCases
        parseTheoInducCases =do
                    keywordIn
                    fc <- parseFocus keywordFor
                    fei <- parseFocus keywordDot
                    [rel] <- manyTill rel keywordDot
                    fef <- parseFocus keywordWith
                    n <- parseProofName
                    addProofNameWithProof n Nothing
                    return n


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

-- | Parser de pruebas.
proof :: Maybe Ctx -> Bool -> ParserP Proof
proof mc flag = do
        many newline
        when (flag) keywordBegin
        when (flag) keywordProof
        p <- case mc of
            Just c  -> parseProofWithName c <|> parseProofWithoutName c
            Nothing ->  parseProofWithName beginCtx 
                    <|> parseProofWithoutName beginCtx
        return p
    where
        parseProofWithName :: Ctx -> ParserP Proof
        parseProofWithName c = parseProofName >>= \n -> many newline >>
                            (   inducProof c
                            <|> casesProof c
                            <|> transProof c flag
                            ) >>= \p -> addProofNameWithProof n (Just p) 
                              >> return p
        parseProofWithoutName :: Ctx -> ParserP Proof
        parseProofWithoutName c = many newline >>
                            (   inducProof c
                            <|> casesProof c
                            <|> transProof c flag
                            )

-- | Parseo de una prueba inductiva.
inducProof :: Ctx -> ParserP Proof
inducProof ctx = do
            keywordInduc
            keywordIn
            fc <- parseFocus keywordFor
            fei <- parseFocus keywordDot
            [rel] <- manyTill rel keywordDot
            fef <- parseFocus keywordWhere
            cs <- manyTill parseCases parseProofEnd
            let p = Ind ctx rel fei fef fc cs
            return p 

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
            cs <- manyTill parseCases parseProofEnd
            let p = Cases ctx rel fei fef fc cs
            return p

-- | Parsea casos.
parseCases :: ParserP (Focus, Proof)
parseCases = do
            fi <- parseFocus keywordRArrow
            p <- proof (Just beginCtx) False
            return (fi,p)

-- | Parser de pruebas transitivas, estan incluidas las pruebas simples.
transProof :: Ctx -> Bool -> ParserP Proof
transProof ctx flag = parseFocus tryNewline >>= \e1 -> 
                 getProofSet >>= \pSet -> 
                 manyExprLine >>= return . (mkTrans ctx e1 pSet)
    where
        parseStep = do
                    rj <- justification
                    e <- parseFocus tryNewline
                    return (e,rj)
        manyExprLine :: ParserP [(Focus,(Relation, Maybe Basic))]
        manyExprLine = do 
                        frb <- parseStep
                        frbs <- if flag 
                                    then manyTill (parseStep) (parseProofEnd)
                                    else many parseStep
                        return (frb:frbs)

-- | Parser de la relación sobre la que estamos haciendo la prueba.
rel :: ParserP Relation
rel = foldr ((<|>) . uncurry prel) parserZero relations
    where prel iden ty = ty <$ (many whites >> try (string iden))
          relations = [("=",relEq), ("≡",relEquiv), ("⇒",relImpl), ("⇐",relCons)]

-- | Parser de prueba.
parsePfFromString' :: String -> Either ParseError [Proof]
parsePfFromString' = either handleError Right . runParser 
                                                (prooflist Nothing) initPState "" 
    where
        -- Esto esta pensando en que hay que hacer algo para obtener bien
        -- la posición del error.
        handleError :: ParseError -> Either ParseError [Proof]
        handleError = Left 

-- Parsea una prueba desde un archivo.
parseFromFileProof :: FilePath -> IO ()
parseFromFileProof fp = readFile fp >>= print . parsePfFromString'

initPState :: PState
initPState = PState M.empty initVarTy
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
mkTrans c e pSet ((e',(r,j)):[]) = mkSimple c r e e' (theoCheck pSet j)
mkTrans c e pSet ((e',(r,j)):steps) = go (mkSimple c r e e' (theoCheck pSet j)) steps
    where 
        go :: Proof -> [(Focus,(Relation, Maybe Basic))] -> Proof
        go p [] = p
        go p ((e,(r, j)):ps) = go prf' ps
            where 
                e0 = fromJust (getStart p)
                e1 = fromJust (getEnd p)
                prf' = Trans c r e0 e1 e p (mkSimple c r e1 e (theoCheck pSet j))

-- | Chequear que un nombre de teorema este declarado antes.
theoCheck :: ProofSet -> Maybe Basic -> Maybe Basic
theoCheck pSet (Just b) = 
    case (b, M.lookup (truthName b) pSet) of
        (Ax _,_) -> Just b
        (Theo theorem, Just (Just p)) -> Just $ Theo $ theoremAddProof p theorem
        (Theo theorem, _) -> error $ "Falta la declaración del teorema " ++ show theorem
