-- | Este modulo es el parser a Pre-Expresiones. 
{--
Sobre Parsec

# Informe de errores; Parece ser que con ParseError nos alcanza.

# Funcion que determina el conName.

# Hace falta hacer algun tipo de analisis para los tipos. Parseando
una funcion no hay problema debido a los constructores definidos en las teorias
pero que pasa con las constantes? por ejemplo, parseExpr 3; deberia quedar
parseado con su tipo? que pasa si el usuario lo especifico o no.
Resolucion: Parseamos con TyUnknown

# Syntaxis de una escritura general; Como es una prueba bien escrita.
Se permiten comentarios?

# Operadores de lista; Presedencia, de momento todos tienen la misma.

# Libreria; criterion para testear rendimiento.
--}

module Equ.Parser where

import Equ.PreExpr as Pe
import Equ.Types
import Equ.Theories.List
import Equ.Theories.Arith
import Equ.Theories.AbsName
import Data.Text as T
import Text.ParserCombinators.Parsec
import Text.Parsec.Token as P
import Text.Parsec.Language
import Text.Parsec.Expr as TPe
import Control.Monad.Identity
import Text.Parsec.Char (oneOf, letter, char, alphaNum)

-- Operadores de listas. Esta lista estaria piola que sea exportada desde List.h
listOperators :: [Pe.Operator]
listOperators = [ listApp
                , listTake
                , listDrop
                , listIndex
                , listConcat
                , listLength
                ]

-- Constantes de listas. Esta lista estaria piola que sea exportada desde List.h
listConsts :: [Constant]
listConsts = [listEmpty]

reprListOperators :: [String]
reprListOperators = fmap (unpack . tRepr) listOperators

-- De momento los nombres reservados tenemos la lista vacia.
-- Tal luego ya no haga falta o queda para extender.
keywords :: [String]
keywords = fmap (unpack . tRepr) listConsts

lang :: TokenParser ()
lang = makeTokenParser $
        emptyDef { reservedOpNames = reprListOperators
                 , reservedNames = keywords
                 , identStart  = letter <|> char '_'
                 , identLetter = alphaNum <|> char '_'
                 , opStart  = (oneOf . Prelude.map Prelude.head) reprListOperators
                 , opLetter = (oneOf . Prelude.concat) reprListOperators
                 }

msymbol = P.symbol lang
mparens = P.parens lang
msquares = P.squares lang
mcomma = P.comma lang

listOpTable :: OperatorTable String () Identity PreExpr
listOpTable = [ [ mkOpBinIn listApp
                , mkOpBinIn listTake
                , mkOpBinIn listDrop
                , mkOpBinIn listIndex
                , mkOpBinIn listConcat
                , mkOpUnPre listLength
                ]
              ]

-- Parsea un simbolo de operador.
oper :: String -> Parser ()
oper s = msymbol s >> return ()

-- Parsea un simbolo de constante.
constant :: String -> Constant -> Parser PreExpr
constant s c = try $ msymbol s >> return (Con c)

-- data Operator tok st a
        -- = Infix (GenParser tok st (a -> a -> a)) Assoc
        -- | Prefix (GenParser tok st (a -> a))
        -- | Postfix (GenParser tok st (a -> a))

-- Crea elemento de OperatorTable. Version para Prefix
mkOpUnPre :: Pe.Operator -> TPe.Operator String () Identity PreExpr
mkOpUnPre op = Prefix ((oper $ unpack $ tRepr op) >> return (UnOp op))

-- Crea elemento de OperatorTable. Version para Infix.
mkOpBinIn :: Pe.Operator -> TPe.Operator String () Identity PreExpr
mkOpBinIn op = Infix ((oper $ unpack $ tRepr op) >> return (BinOp op)) (assoc op)

-- Mapeo entre nuestros tipo de assoc y el de parsec.expr .
assoc :: Pe.Operator -> TPe.Assoc
assoc op = case (opAssoc op) of
            None -> AssocNone
            ALeft -> AssocLeft
            ARight -> AssocRight

-- Parseo de enteros.
int :: Parser Int
int = (integer lang >>= return . fromInteger) <?> "\"Num\""

-- Parseo de enteros preExpr.
intcon :: Parser PreExpr
intcon = int >>= return . intToCon

-- Parseo de parentesis preExpr.
preExprParen :: Parser PreExpr -> Parser PreExpr
preExprParen ppe = mparens ppe >>= return . Paren

-- Parseo de la lista escrita con syntax sugar.
sugarList :: Parser PreExpr
sugarList = do { x <- preExprList ;
                 xs <- ((mcomma <?> "\",\"") >> sugarList) <|> return (Con listEmpty);
                 return $ BinOp listApp x xs;
            }

-- Parsers necesarios (Hasta el momento) para parsear listas.
listAtom :: [Parser PreExpr]
listAtom = [ preExprParen preExprList -- Parentesis.
           , intcon -- Numeros.
           , constant "[ ]" listEmpty -- Lista vacia.
           , msquares sugarList -- Lista escrita con syntax sugar; ie: [_,...,_]
           ]

preExprList :: Parser PreExpr
-- buildExpressionParser :: OperatorTable tok st a -> GenParser tok st a -> GenParser tok st a
preExprList = buildExpressionParser listOpTable (choice listAtom) <?> "Expression"

parseFromString :: String -> Either ParseError PreExpr
-- runParser :: GenParser tok st a -> st -> FilePath -> [tok] -> Either ParseError a
parseFromString = runParser preExprList () ""

parseExpr :: String -> PreExpr
parseExpr = either showError id . parseFromString

showError :: Show a => a -> b
showError = (error . show)

-- | Este tipo representa todos los posibles errores de parseo.
-- TODO: Extender según la necesidad; recordar guardar la información
-- sobre posiciones del error.
-- data ParseError = ParseError

-- | Obviamente, la función principal de este módulo. Probablemente
-- necesitemos una función más general que tenga en cuenta el contexto
-- en el que queremos parsear algo para de esa manera poder dar
-- errores informativos.
parser :: Text -> Either ParseError PreExpr
parser = undefined

-- | Para definir la función anterior podemos necesitar definir 
-- esta función para poder parsear los tipos que el usuario quiera
-- asignar a los diferentes constituyentes de pre-expresiones.
parserTy :: Text -> Either ParseError Type
parserTy = undefined
