-- | Este modulo es el parser de pruebas.
module Equ.Parser.Proof (parsePfFromString') where

import Equ.Parser.Expr
import Equ.PreExpr (toFocus,Focus,unParen)
import Equ.Proof (validateProof)
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
import Text.Parsec.Token
import Text.Parsec.Language
import Text.Parsec.String
import qualified Text.Parsec.Expr as PE

import Data.Maybe
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
exprLine :: Parser' Focus
exprLine = spaces >> parsePreExpr >>= return . toFocus . unParen

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
                optionMaybe (braced basic) >>= \j -> return (r, j) -- <$ newLine)

-- | Puesto que las expresiones pueden tener múltiples líneas, tomamos
-- como fin de una expresión el string "¿". Este es un horrendo hack,
-- que hay que corregir.
weirdSep p = p >>= \r -> optional (string "¿\n") >> return r

-- | Parser una paso simple. No es necesario, porque lo 
-- tratamos también en 'trans'.
simple :: Parser' Proof
simple = do e <- weirdSep exprLine            
            (r,j) <- weirdSep justification
            e' <- weirdSep exprLine
            return (mkSimple beginCtx r e e' j)


-- | Parser de pruebas con uno o más pasos.
trans :: Parser' Proof
trans = weirdSep exprLine >>= \e1 ->
        many1 (weirdSep justification >>= \j -> 
               weirdSep exprLine >>= \e -> 
               return (e,j)) >>=
        return . mkTrans beginCtx e1

-- | Parser de pruebas; se puede simplificar descartando la opción 'simple'.
proof :: Parser' Proof
proof = try trans <|> simple

-- | Parser de la relación sobre la que estamos haciendo la prueba.
rel :: Parser' Relation
rel = foldr ((<|>) . uncurry prel) parserZero relations
    where prel iden ty = ty <$ (try $ string iden)
          relations = [("=",relEq), ("≡",relEquiv), ("⇒",relImpl), ("⇐",relCons)]

-- | Parser de prueba.
parsePfFromString' :: String -> Either ParseError Proof
parsePfFromString' = runParser proof (0,M.empty) "TEST" 

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
