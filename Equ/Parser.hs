-- | Este modulo es el parser a Pre-Expresiones. 
{--
Sobre Parsec

-- Informe de errores; Quisieramos poder marcar la posicion del error
e informacion bonita de cual fue el error. Parece ser que con
ParseError nos alcanza.

-- Funcion que determina el conName.

-- Hace falta hacer algun tipo de analisis para los tipos. Parseando
una funcion no hay problema debido a los constructores definidos en
las teorias pero que pasa con las constantes? por ejemplo, parseExpr
3; deberia quedar parseado con su tipo? que pasa si el usuario lo
especifico o no.  Resolucion: Parseamos con TyUnknown

-- Syntaxis de una escritura general; Como es una prueba bien escrita.
Se permiten comentarios?

-- Operadores de lista; Precedencia, de momento todos tienen la misma.

-- Libreria; criterion para testear rendimiento.
--}

module Equ.Parser where

import Text.Parsec
import Text.Parsec.Token
import Text.Parsec.Language
import qualified Text.Parsec.Expr as PE
import Data.Text (pack,unpack)
import Data.List(group,sort)
import Data.Map (Map,insert,member,(!))
import qualified Data.Map as M
import Control.Monad.Identity
import Control.Applicative ((<$>),(<$),(<*>))

import Equ.Theories
import Equ.Syntax
import Equ.PreExpr.Internal
import Equ.Types
import Equ.Theories.List(listApp, listEmpty)
import Equ.Theories.Arith(intToCon)
import Equ.Parser.Types(listAtomTy)

data PError = UnOpNotApplied Operator 
            | BinOpNotApplied Operator

type VarTy = (Int,Map (Either VarName FuncName) Type)

type PState = VarTy

type ParserTable = PE.OperatorTable String PState Identity PreExpr
type Parser' a = ParsecT String PState Identity a
type ParserOper = PE.Operator String PState Identity PreExpr

-- | Inicio de una cuantificaci&#243;n.
quantInit :: String
quantInit = "〈"

-- | Final de una cuantificaci&#243;n.
quantEnd :: String
quantEnd = "〉"

-- | Separador de la cuantificaci&#243;n.
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
rNames = [quantInit,quantEnd,quantSep,"-"] 
         ++ map (unpack . conRepr) constantsList
         ++ map (unpack . quantRepr) quantifiersList
         ++ listAtomTy
         

lexer :: TokenParser PState
lexer = makeTokenParser $
            emptyDef { reservedOpNames = rOpNames
                     , reservedNames = rNames
                     , identStart  = letter
                     , identLetter = alphaNum <|> char '_'
                     }

parsePreExpr :: Parser' PreExpr
parsePreExpr = PE.buildExpressionParser operatorTable subexpr 
               <?> "Parser error: Expresi&#243;n mal formada"

-- Construimos la table que se le pasa a buildExpressionParser:
-- Primero agregamos el operador aplicaci&#243;n, que precede a cualquier otro
operatorTable :: ParserTable
operatorTable = [parserApp] : makeTable operatorsList
    where parserApp = PE.Infix (App <$ reservedOp lexer opApp) PE.AssocLeft

makeTable :: [Operator] -> ParserTable
makeTable = map makeSubList . group . reverse . sort 

makeOp :: Operator -> ParserOper
makeOp op = case opNotationTy op of 
              NPrefix  -> PE.Prefix  $ UnOp op <$ parseOp
              NPostfix -> PE.Postfix $ UnOp op <$ parseOp
              NInfix   -> PE.Infix   (BinOp op <$ parseOp) assoc
    where parseOp = (reservedOp lexer . unpack . opRepr $ op)
--                    putState (UnOp op $ PrExHole . hole . pack $ "")
          assoc = convertAssoc . opAssoc $ op

makeSubList :: [Operator] -> [ParserOper]
makeSubList = map makeOp

convertAssoc :: Assoc -> PE.Assoc
convertAssoc None = PE.AssocNone
convertAssoc ALeft = PE.AssocLeft
convertAssoc ARight = PE.AssocRight

-- Parseamos las subexpresiones
-- Una expresion puede ser una expresion con parentesis, una constante, una expresion cuantificada,
-- una variable, una funci&#243;n o una expresion que viene desde un parseo por syntactic sugar
subexpr :: Parser' PreExpr
subexpr = Paren <$> parens lexer parsePreExpr
          <|> parseConst constantsList
          <|> parseQuant quantifiersList
          <|> parsePreExprVar parseVar
          <|> parsePreExprFunc parseFunc
          <|> parseHole
          <|> parseSugarPreExpr parsePreExpr
                            
-- Parseo de Constantes definidas en la teoria

-- Vamos juntando las opciones de parseo de acuerdo a cada constante en la lista.
-- En el caso en que la lista es vacia, la opcion es un error
parseConst :: [Constant] -> Parser' PreExpr
parseConst = foldr pConst $ fail "Constante"
    where pConst c = (<|>) $ reserved lexer (unpack $ conRepr c) >> return (Con c)
   
-- Parseo de Cuantificadores definidos en la teoria
parseQuant :: [Quantifier] -> Parser' PreExpr
parseQuant = foldr pquant $ fail "Cuantificador"
    where pquant q = ( pQuan q <|>)

pQuan :: Quantifier -> Parser' PreExpr
pQuan q = try $ symbol lexer quantInit >>
          (symbol lexer . unpack . quantRepr) q >>
          (parseVar <?> "Cuantificador sin variable") >>= 
          \v -> symbol lexer quantSep >> parsePreExpr >>=
          \r -> symbol lexer quantSep >> parsePreExpr >>=
          \t -> symbol lexer quantEnd >> return (Quant q v r t)

-- Parseo de huecos.
parseHole :: Parser' PreExpr
parseHole = PrExHole . hole . pack <$> 
                (try $ reserved lexer opHole >> braces lexer parseInfo)
            <|> fail "Hueco"

-- Parseo de la informacion de un hueco.
parseInfo :: Parser' String
parseInfo = many $ letter <|> space


-- Calcula el tipo de una variable o funcion
setType :: (Either VarName FuncName) -> PState -> (PState,Type)
setType name (n,st) = if name `M.member` st
                      then ((n,st), st ! name)
                      else ((n+1, insert name newvar st), newvar)
    where newvar = tyVar $ "VInt" ++ show n

-- Parseo de expresiones variable
parsePreExprVar :: Parser' Variable -> Parser' PreExpr
parsePreExprVar = (Var <$>)

-- Esta funcion parsea una variable. Nos fijamos que empiece con
-- minuscula para distinguirla de las funciones (que empiezan con
-- mayuscula). 
parseVar :: Parser' Variable
parseVar = try $ lexeme lexer ((:) <$> lower <*> many letter) >>= 
           \v -> getState >>= 
           \st -> return (setType (Left $ pack v) st) >>=
           \(st',t) -> putState st' >> 
           return Variable { varName = pack v 
                           , varTy = t
                           }

-- Parseo de expresiones funcion
parsePreExprFunc :: Parser' Func -> Parser' PreExpr
parsePreExprFunc = (Fun <$>)

-- Parseo de funciones. Un s&#237;mbolo de funcion es un string que empieza
-- con may&#250;scula.
parseFunc :: Parser' Func
parseFunc = try $ lexeme lexer ((:) <$> upper <*> many letter) >>=
            \f -> getState >>=
            \st -> return (setType (Right $ pack f) st) >>=
            \(st',t) -> putState st' >>
            return Func { funcName= pack f
                        , funcTy= t
                        }



-- //////// Parser de syntax sugar ////////

-- Parseo de expresiones azucaradas.
parseSugarPreExpr :: Parser' PreExpr -> Parser' PreExpr
parseSugarPreExpr p = parseSugarList p <|> parseIntPreExpr

-- | Parseo de la lista escrita con syntax sugar.
sugarList :: Parser' PreExpr -> Parser' PreExpr
sugarList p = foldl (BinOp listApp) (Con listEmpty) <$> (p `sepBy` char ',')

-- | Parseo de la lista escrita con syntax sugar.
parseSugarList :: Parser' PreExpr -> Parser' PreExpr
parseSugarList = brackets lexer . sugarList

-- | Parseo de una funci&#243;n aplicada: f(a,b)
parseSugarApp :: Parser' PreExpr
parseSugarApp = undefined 

-- | Parseo de enteros.
parseInt :: Parser' Int
parseInt = fromInteger <$> natural lexer <?> fail "Numero"

-- | Parseo de enteros preExpr.
parseIntPreExpr :: Parser' PreExpr
parseIntPreExpr = intToCon <$> parseInt

-- //////// Parser de syntax sugar ////////

-- | Funcion principal de parseo desde string.
parseFromString :: String -> Either ParseError PreExpr
parseFromString = runParser parsePreExpr (0,M.empty) "TEST" 

-- | Funcion principal de parseo.
parser :: String -> PreExpr
parser = either showError showPreExpr . parseFromString

-- Imprimimos el error con version Exception de haskell.
showError :: Show a => a -> b
showError = error . show

-- Imprimimos la preExpresion, usando que tenemos definido la instancia show.
showPreExpr :: a -> a
showPreExpr = id
