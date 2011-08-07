-- Miguel: el módulo debería tener un nombre que coincida con el 
--   del archivo; debería haber una lista con las entidades que 
--   exportamos (pueden ver Equ.Theories.List para usarlo como 
--   ejemplo; de paso pueden ver cómo documentar para que haddock
--   haga páginas bonitas). 

-- parser de prueba para parsear expresiones en la teoria FOL:
module Equ.ParserFOL where
import Text.Parsec
import Text.Parsec.Token
import Text.Parsec.Language
import Text.Parsec.String
-- Miguel: usar nombres cortos puede ayudar a tener líneas cortas.
import qualified Text.Parsec.Expr as PE
import Data.Text (pack,unpack)
import Data.List
import Data.Char
import Control.Monad.Identity

-- Miguel: Excepto que haya muchas cosas importadas de un módulo
-- puede ayudar que los enumeremos caso por caso.
import Equ.Theories
import Equ.Syntax
import Equ.PreExpr
import Equ.Types

-- Miguel: No tienen declaración de tipos.
-- Para los cuantificadores:
quantInit = "〈"
quantEnd = "〉"
quantSep = ":"

-- Miguel: No tiene declaración de tipo.
-- Operador para la aplicacion:
opApp = "@"


-- Miguel: Tal vez se pueda hacer declaraciones locales:
--    operators = opApp : map ...
lexer :: TokenParser ()
lexer = makeTokenParser $
            emptyDef { reservedOpNames = opApp : map (unpack . opRepr) operatorsList
                     , reservedNames = [quantInit,quantEnd,quantSep,"-"] 
                                       ++ map (unpack . conRepr) constantsList 
                                       ++ map (unpack .quantRepr) quantifiersList
                     , identStart  = letter <|> char '_'
                     , identLetter = alphaNum <|> char '_'
                     }

-- Miguel: tratemos de no tener líneas de más de 80 columnas.
parseExpr :: Parser PreExpr
parseExpr = PE.buildExpressionParser operatorTable subexpr 
            <?> "Parser error: Expresión mal formada"

-- Miguel: algunas abreviaciones de tipo son útiles.
type ParserTable = PE.OperatorTable String () Identity PreExpr
type ParserOper = PE.Operator String () Identity PreExpr

-- Construimos la table que se le pasa a buildExpressionParser:
-- Primero agregamos el operador aplicación, que precede a cualquier otro
operatorTable :: ParserTable
operatorTable = [parserApp] : makeTable operatorsList
    where parserApp = PE.Infix (reservedOp lexer opApp >> return App) PE.AssocLeft

-- Miguel: si hlint no dijo de reescribir esta función, me sorprende.
makeTable :: [Operator] -> ParserTable
makeTable = map makeSubList . group . reverse . sort 

-- Miguel: uso de declaraciones locales para hacer más claro el código.
-- Acá debemos entender una sóla vez lo que hacer parseOp; mientras que
-- en la versión anterior estaba el mismo código repetido tres veces y
-- nos puede llevar un tiempo leerlo y darnos cuenta que es el mismo.
makeOp :: Operator -> ParserOper
makeOp op = case opNotationTy op of 
              NPrefix  -> PE.Prefix  $ parseOp >> return (UnOp op)
              NPostfix -> PE.Postfix $ parseOp >> return (UnOp op)
              NInfix   -> PE.Infix   (parseOp >> return (BinOp op)) assoc
    where parseOp = reservedOp lexer . unpack . opRepr $ op
          assoc = convertAssoc . opAssoc $ op

-- Miguel: no es buena idea ocultar una función interesante (makeOp en
-- este caso) dentro de otra función. 
makeSubList :: [Operator] -> [ParserOper]
makeSubList = map makeOp

convertAssoc :: Assoc -> PE.Assoc
convertAssoc None = PE.AssocNone
convertAssoc ALeft = PE.AssocLeft
convertAssoc ARight = PE.AssocRight

-- Parseamos las subexpresiones
-- Una expresion puede ser una expresion con parentesis, una
-- constante, una expresion cuantificada, una variable, una función o
-- una expresion que viene desde un parseo por syntactic sugar
subexpr :: Parser PreExpr
subexpr = fmap Paren (parens lexer parseExpr)
          <|>  parseConst constantsList
          <|>  parseQuant quantifiersList
          <|>  parseExprVar
          <|>  parseFunc
          <|>  parseSugarExpr parseExpr
                            
-- Parseo de Constantes definidas en la teoria

-- Miguel: pConst (el nombre podría ser mejor) es la función interesante
--    acá. No la pongo como una función de primer nivel porque sólo es útil
--    en este punto.
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
                    \v -> reserved lexer quantSep >> parseExpr >>=
                    \r -> reserved lexer quantSep >> parseExpr >>=
                    \t -> reserved lexer quantEnd >> return (Quant q v r t)
               


-- Miguel: No entiendo porqué la generalidad que tenía antes (parseVar era
--   un argumento).
-- Parseo de expresiones variable
parseExprVar :: Parser PreExpr
parseExprVar = parseVar >>= return . Var

-- Miguel: los dos parsers no me gustan desde el día que los programé :) .
--    Ya me voy a dar cuenta cómo escribirlos.
-- Esta funcion parsea una variable. Nos fijamos que empiece con
-- minuscula para distinguirla de las funciones (que empiezan con
-- mayuscula). La idea es tomada de Yahc.
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

parseSugarExpr :: Parser PreExpr -> Parser PreExpr
parseSugarExpr = undefined

-- Funcion principal de parseo
parser :: String -> Either ParseError PreExpr
parser = parse parseExpr ""


-- Expresiones de prueba:
-- (F@(succ 0) + x) ▹ [] ⇒ True
-- 〈 ∃ x : (G@(# []) + x) ▹ [] ⇒ True : p ⇒ q 〉

