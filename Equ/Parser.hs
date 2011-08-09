-- | Este modulo es el parser a Pre-Expresiones. 
{--
Sobre Parsec

-- Informe de errores; Quisieramos poder marcar la posicion del error e 
informacion bonita de cual fue el error. Parece ser que con ParseError nos alcanza.

-- Funcion que determina el conName.

-- Hace falta hacer algun tipo de analisis para los tipos. Parseando
una funcion no hay problema debido a los constructores definidos en las teorias
pero que pasa con las constantes? por ejemplo, parseExpr 3; deberia quedar
parseado con su tipo? que pasa si el usuario lo especifico o no.
Resolucion: Parseamos con TyUnknown

-- Syntaxis de una escritura general; Como es una prueba bien escrita.
Se permiten comentarios?

-- Operadores de lista; Presedencia, de momento todos tienen la misma.

-- Libreria; criterion para testear rendimiento.
--}

module Equ.Parser where

import Text.Parsec
import Text.Parsec.Token
import Text.Parsec.Language
import Text.Parsec.String
import qualified Text.Parsec.Expr as PE
import Data.Text (pack,unpack)
import Data.List
import Data.Char
import Control.Monad.Identity

import Equ.Theories
import Equ.Syntax
import Equ.PreExpr
import Equ.Types
import Equ.Theories.List(listApp, listEmpty)
import Equ.Theories.Arith(intToCon)

type ParserTable = PE.OperatorTable String () Identity PreExpr
type ParserOper = PE.Operator String () Identity PreExpr

-- | Inicio de una cuantificación.
quantInit :: String
quantInit = "〈"

-- | Final de una cuantificación.
quantEnd :: String
quantEnd = "〉"

-- | Separador de la cuantificación.
quantSep :: String
quantSep = ":"

-- | Operador para la aplicacion.
opApp :: String
opApp = "@"

holeInfoInit :: String
holeInfoInit = "{"

holeInfoEnd :: String
holeInfoEnd = "}"

opHole :: String
opHole = "?"

-- | Representantes de los operadores. (Salvo para aplicacion)
rOpNames :: [String]
rOpNames = opApp : opHole : map (unpack . opRepr) operatorsList

-- | Representantes de las constantes y cuantificadores.
-- Ademas de los caracteres para representar expresiones cuantificadas.
rNames :: [String]
rNames = [quantInit,quantEnd,quantSep,"-"] ++ 
         map (unpack . conRepr) constantsList ++
         map (unpack .quantRepr) quantifiersList

lexer :: TokenParser ()
lexer = makeTokenParser $
            emptyDef { reservedOpNames = rOpNames
                     , reservedNames = rNames
                     , identStart  = letter <|> char '_'
                     , identLetter = alphaNum <|> char '_'
                     }

parsePreExpr :: Parser PreExpr
parsePreExpr = PE.buildExpressionParser operatorTable subexpr 
               <?> "Parser error: Expresión mal formada"

-- Construimos la table que se le pasa a buildExpressionParser:
-- Primero agregamos el operador aplicación, que precede a cualquier otro
operatorTable :: ParserTable
operatorTable = [parserApp] : makeTable operatorsList
    where parserApp = PE.Infix (reservedOp lexer opApp >> return App) PE.AssocLeft

makeTable :: [Operator] -> ParserTable
makeTable = map makeSubList . group . reverse . sort

makeOp :: Operator -> ParserOper
makeOp op = case opNotationTy op of 
              NPrefix  -> PE.Prefix  $ parseOp >> return (UnOp op)
              NPostfix -> PE.Postfix $ parseOp >> return (UnOp op)
              NInfix   -> PE.Infix    (parseOp >> return (BinOp op)) assoc
    where parseOp = reservedOp lexer . unpack . opRepr $ op
          assoc = convertAssoc . opAssoc $ op

makeSubList :: [Operator] -> [ParserOper]
makeSubList = map makeOp

convertAssoc :: Assoc -> PE.Assoc
convertAssoc None = PE.AssocNone
convertAssoc ALeft = PE.AssocLeft
convertAssoc ARight = PE.AssocRight

-- Parseamos las subexpresiones
-- Una expresion puede ser una expresion con parentesis, una constante, una expresion cuantificada,
-- una variable, una función o una expresion que viene desde un parseo por syntactic sugar
subexpr :: Parser PreExpr
subexpr = fmap Paren (parens lexer parsePreExpr)
          <|>  parseConst constantsList
          <|>  parseQuant quantifiersList
          <|>  parsePreExprVar parseVar
          <|>  parseFunc
          <|>  parseHole
          <|>  parseSugarPreExpr parsePreExpr
                            
-- Parseo de Constantes definidas en la teoria

-- Vamos juntando las opciones de parseo de acuerdo a cada constante en la lista.
-- En el caso en que la lista es vacia, la opcion es un error
parseConst :: [Constant] -> Parser PreExpr
parseConst = foldr pConst (fail "Parser error: Expresion mal formada")
    where pConst c =  (<|>) $ reserved lexer (unpack $ conRepr c) >> return (Con c)
   
-- Parseo de Cuantificadores definidos en la teoria
parseQuant :: [Quantifier] -> Parser PreExpr
parseQuant = foldr pQuan (fail "Parse error: Expresi\243n mal formada")
    where pQuan q = (<|>) $ try $ 
                    reserved lexer quantInit >>
                    reserved lexer (unpack $ quantRepr q) >>
                    (parseVar <?> "Cuantificador sin variable") >>=
                    \v -> reserved lexer quantSep >> parsePreExpr >>=
                    \r -> reserved lexer quantSep >> parsePreExpr >>=
                    \t -> reserved lexer quantEnd >> return (Quant q v r t)

-- Parseo de huecos.
parseHole :: Parser PreExpr
parseHole = (try $ reserved lexer opHole >> 
                ((braces lexer parseInfo >>= \i ->
                  return (PrExHole $ hole (pack i)))
                  <|>
                  return (PrExHole $ hole (pack ""))))
            <|>
            (fail "Parse error: Expresi\243n mal formada")

-- Parseo de la informacion de un hueco.
parseInfo :: Parser String
parseInfo = many1 (letter <|> space)

-- Parseo de expresiones variable
parsePreExprVar :: Parser Variable -> Parser PreExpr
parsePreExprVar pars_v = pars_v >>= \v -> return (Var v)

-- Esta funcion parsea una variable. Nos fijamos que empiece con minuscula para distinguirla
-- de las funciones (que empiezan con mayuscula). La idea es tomada de Yahc.
parseVar :: Parser Variable
parseVar = try $ identifier lexer >>= \s -> if (not . null) s && (isLower . head) s
                                           then return Variable { varName= pack s
                                                                , varTy= TyUnknown
                                                                }
                                           else parserZero

-- Parseo de funciones
-- Una simbolo de funcion es un string que empieza con mayúscula.
parseFunc :: Parser PreExpr
parseFunc = identifier lexer >>= \s -> if (not . null) s && (isUpper . head) s
                                           then return . Fun $ Func { funcName= pack s
                                                                    , funcTy= TyUnknown
                                                                    }
                                           else parserZero


-- //////// Parser de syntax sugar ////////

-- Parseo de expresiones azucaradas.
parseSugarPreExpr :: Parser PreExpr -> Parser PreExpr
parseSugarPreExpr p = parseSugarList p <|> parseIntPreExpr

-- | Parseo de la lista escrita con syntax sugar.
sugarList :: Parser PreExpr -> Parser PreExpr
sugarList p = do {  x <- p;
                    xs <- ((comma lexer <?> "\",\"") >> sugarList p) 
                        <|> return (Con listEmpty);
                    return $ BinOp listApp x xs;
                 }

-- | Parseo de la lista escrita con syntax sugar.
parseSugarList :: Parser PreExpr -> Parser PreExpr
parseSugarList p = brackets lexer (sugarList p)

-- | Parseo de enteros.
parseInt :: Parser Int
parseInt = fmap fromInteger (integer lexer) <?> "Numero"

-- | Parseo de enteros preExpr.
parseIntPreExpr :: Parser PreExpr
parseIntPreExpr = fmap intToCon parseInt

-- //////// Parser de syntax sugar ////////

-- | Funcion principal de parseo desde string.
parseFromString :: String -> Either ParseError PreExpr
parseFromString = parse parsePreExpr ""

-- | Funcion principal de parseo.
parser :: String -> PreExpr
parser = either showError showPreExpr . parseFromString

-- Imprimimos el error con version Exception de haskell.
showError :: Show a => a -> b
showError = error . show

-- Imprimimos la preExpresion, usando que tenemos definido la instancia show.
showPreExpr :: a -> a
showPreExpr = id

-- | Este tipo representa todos los posibles errores de parseo.
-- TODO: Extender según la necesidad; recordar guardar la información
-- sobre posiciones del error.
-- data ParseError = ParseError

-- | Obviamente, la función principal de este módulo. Probablemente
-- necesitemos una función más general que tenga en cuenta el contexto
-- en el que queremos parsear algo para de esa manera poder dar
-- errores informativos.
-- parser :: Text -> Either ParseError PreExpr
-- parser = undefined

-- | Para definir la función anterior podemos necesitar definir 
-- esta función para poder parsear los tipos que el usuario quiera
-- asignar a los diferentes constituyentes de pre-expresiones.
-- parserTy :: Text -> Either ParseError Type
-- parserTy = undefined

-- Expresiones de prueba:
-- (F@(succ 0) + x) ▹ [] ⇒ True
-- 〈∃ x : (G@(# []) + x) ▹ [] ⇒ True : p ⇒ q〉

