-- | Este modulo es el parser de pruebas.
module Equ.Parser.Proof (parsePfFromString',rel,proof) where

import Equ.Parser.Expr
import Equ.PreExpr (PreExpr,toFocus,Focus,unParen)
import Equ.Proof (validateProof, printProof)
import Equ.Proof.Proof ( Proof'(..)
                       , Ctx
                       , Basic (..) 
                       , Theorem (..)
                       , Axiom (..)
                       , getEnd 
                       , getStart
                       , beginCtx
                       , Proof)
import Equ.Theories (theories,axiomGroup,TheoryName,createTheorem)
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
import qualified Data.Map as M (empty) 

import Control.Monad.Identity
import Control.Applicative ((<$>),(<$))

-- | Parser de un axioma, con nombre de teoría.
axiomQual :: [TheoryName] -> Parser' Axiom
axiomQual ths = pTheory >>= \thy -> 
                if thy `elem` ths 
                then char '.' >> 
                    (choice . map axiomInList . fromJust . lookup thy) axiomGroup
                else parserZero
                
-- | Parser de un axioma sin tener en cuenta la teoría.
axiomUnQual :: [TheoryName] -> Parser' Axiom
axiomUnQual ths = (choice . map axiomInList . concatMap snd) axiomGroup

-- | Construcción del parser a partir del axioma.
axiomInList :: Axiom -> Parser' Axiom
axiomInList ax = try $ (string . unpack . axName) ax >> return ax

-- | Parser del nombre de una teoría; notar que el conjunto de teorías
-- conocidas está definido en 'Equ.Theories.theories'
pTheory :: Parser' TheoryName
pTheory = choice (map (string . unpack) theories) >>= return . pack

-- | Si el tipo 'a' tiene un campo 'Text', generamos un parser para
-- ese tipo. Esta es la versión lifteada a listas de 'a'.
anyText :: (a -> Text) -> [a] -> Parser' a
anyText f = choice . map el
    where el a = a <$ (try . string . unpack . f) a

-- | Parsea la declaración de una entidad.
declaration :: String -> Parser' String
declaration decl = string ("new " ++ decl  ++ " ")  >> spaces >>
                   concat <$> endBy (many (noneOf "\n")) newline

-- | Parser para la definición de un teorema; notar que no se
-- valida la prueba.
declTheorem :: Parser' Theorem
declTheorem = declaration "theorem" >>= \thName ->
              proof >>= \thPrf -> 
              return (createTheorem (pack thName) thPrf)

-- | Parser para una lista de teoremas.
prelude :: Parser' [Theorem]
prelude = sepBy declTheorem (newline >> newline)

-- | Parser de una sesión. 
-- TODO: considerar que un teorema dependa de los teoremas 
-- previamente definidos; considerar declaración de hipótesis.
session :: Parser' ([Theorem],Ctx,Proof)
session = prelude >>= \ths ->          
          proof >>= \prf ->
          return (ths,beginCtx,prf)

-- | Parser del uso de un teorema; notar que necesitamos la lista de 
-- teoremas conocidos en este momento.
theorem :: [Theorem] -> Parser' Theorem
theorem = anyText thName

-- | Uso del parser de una expresión definido en 'Equ.Parser.Expr'.
-- Ale: No esta bonito como manejamos el pasaje de errores con pass
-- ademas pasa que tenemos que re-acomodar la posición del error.
-- Algo raro es que la posición de la linea siempre esta un lugar mas "adelante"
exprLine :: Parser' Focus
exprLine = manyTill anyChar (try (char '\n')) >>= return . exprL >>= pass
    where
        pass :: Either ParseError Focus -> Parser' Focus
        pass ef = case ef of
                        Right e -> return e
                        Left per -> getPosition >>= \p -> 
                                    fail $ show $ flip setErrorPos per $
                                    setSourceLine (errorPos per) (sourceLine p-1)
        exprL' :: Parser' Focus
        exprL' = spaces >> parsePreExpr >>= return . toFocus . unParen
        exprL :: String -> Either ParseError Focus
        exprL = runParser exprL' (0,M.empty) ""
        

-- | Parser de una justificación inmediata de un paso de prueba.
-- TODO: considerar hipótesis.
basic :: Parser' Basic
basic = (axiomUnQual theories >>= return . Ax)
        <|> (theorem [] >>= return . Theo)

-- | Parser de entidades entre llaves.
braced :: Parser' a -> Parser' a
braced = between (string "{" >> spaces) (spaces >> string "}" )

-- | Parser de un paso de prueba.
justification :: Parser' (Relation, Maybe Basic)
justification = rel >>= \r -> spaces >>
                optionMaybe (braced basic) >>= \j -> 
                char '\n' >> return (r, j)

-- | Parser de pruebas.
proof :: Parser' Proof
proof = proof'
    where
        proof' :: Parser' Proof
        proof' = exprLine >>= \e1 -> manyExprLine >>= return.mkTrans beginCtx e1
        manyExprLine :: Parser' [(Focus,(Relation, Maybe Basic))]
        manyExprLine = many1 (justification >>= \rj -> exprLine >>= \e -> return (e,rj))

-- | Parser de la relación sobre la que estamos haciendo la prueba.
rel :: Parser' Relation
rel = foldr ((<|>) . uncurry prel) parserZero relations
    where prel iden ty = ty <$ (try $ string iden)
          relations = [("=",relEq), ("≡",relEquiv), ("⇒",relImpl), ("⇐",relCons)]

-- | Parser de prueba.
parsePfFromString' :: String -> Either ParseError Proof
parsePfFromString' = either (handleError) (Right).runParser proof (0,M.empty) "" 
    where
        -- Esto esta pensando en que hay que hacer algo para obtener bien
        -- la posición del error.
        handleError :: ParseError -> Either ParseError Proof
        handleError = Left 

{- Pasar estas funciones a Equ.Proof -}
-- | construcción de una prueba simple.
mkSimple :: Ctx -> Relation -> Focus -> Focus -> Maybe Basic -> Proof
mkSimple c r e e' = maybe (Hole c r e e') (Simple c r e e')

-- | Construcción de una prueba transitiva; estas pruebas son
-- up-leaning, en el sentido que construyen pruebas donde el último
-- paso es simple mientras que todos los demás son transitivos.
mkTrans :: Ctx -> Focus -> [(Focus,(Relation, Maybe Basic))] -> Proof
mkTrans c e [] = error "impossible"
mkTrans c e ((e',(r,j)):[]) = mkSimple c r e e' j
mkTrans c e ((e',(r,j)):steps) = go (mkSimple c r e e' j) steps
    where go :: Proof -> [(Focus,(Relation, Maybe Basic))] -> Proof
          go p [] = p
          go p ((e,(r,j)):ps) = go prf' ps
              where e0 = fromJust (getStart p)
                    e1 = fromJust (getEnd p)
                    prf' = Trans c r e0 e1 e p (mkSimple c r e1 e j)
