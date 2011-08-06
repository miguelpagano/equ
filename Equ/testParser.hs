-- parser de prueba para parsear expresiones en la teoria FOL:

import Text.Parsec
import Text.Parsec.Token
import Text.Parsec.Language
import Text.Parsec.String
import qualified Text.Parsec.Expr as ParsecExpr
import Data.Text (pack,unpack)
import Data.List
import Data.Char
import Control.Monad.Identity

--import Equ.Theories.List
import Equ.Theories
import Equ.Syntax
import Equ.PreExpr
import Equ.Types


-- Para los cuantificadores:
quantInit = "〈"
quantEnd = "〉"
quantSep = ":"

-- Operador para la aplicacion:
opApp = "@"

lexer :: TokenParser ()
lexer = makeTokenParser $
            emptyDef { reservedOpNames = opApp : map (unpack . opRepr) operatorsList
                     , reservedNames = [quantInit,quantEnd,quantSep,"-"] ++ 
                       map (unpack . conRepr) constantsList ++
                       map (unpack .quantRepr) quantifiersList
                     , identStart  = letter <|> char '_'
                     , identLetter = alphaNum <|> char '_'
            }

parseExpr :: Parser PreExpr
parseExpr = ParsecExpr.buildExpressionParser operatorTable subexpr <?> "Parser error: Expresión mal formada"


-- Construimos la table que se le pasa a buildExpressionParser:
-- Primero agregamos el operador aplicación, que precede a cualquier otro

operatorTable :: ParsecExpr.OperatorTable String () Identity PreExpr
operatorTable = [ParsecExpr.Infix (reservedOp lexer opApp >> return App) ParsecExpr.AssocLeft] :
                makeTable operatorsList


makeTable :: [Operator] -> ParsecExpr.OperatorTable String () Identity PreExpr
makeTable l = map makeSubList (group $ reverse $ sort l)

makeSubList :: [Operator] -> [ParsecExpr.Operator String () Identity PreExpr]
makeSubList [] = []
makeSubList (op:ops) =  case op of
                             Operator {opNotationTy=NPrefix} ->
                                ParsecExpr.Prefix (reservedOp lexer (unpack $ opRepr op) >> return (UnOp op)) : makeSubList ops
                             Operator {opNotationTy=NPostfix} ->
                                ParsecExpr.Postfix (reservedOp lexer (unpack $ opRepr op) >> return (UnOp op)) : makeSubList ops
                             otherwise ->
                                ParsecExpr.Infix (reservedOp lexer (unpack $ opRepr op) >> return (BinOp op)) (convertAssoc $ opAssoc op) : makeSubList ops

convertAssoc :: Assoc -> ParsecExpr.Assoc
convertAssoc None = ParsecExpr.AssocNone
convertAssoc ALeft = ParsecExpr.AssocLeft
convertAssoc ARight = ParsecExpr.AssocRight

-- Parseamos las subexpresiones
-- Una expresion puede ser una expresion con parentesis, una constante, una expresion cuantificada,
-- una variable, una función o una expresion que viene desde un parseo por syntactic sugar
subexpr :: Parser PreExpr
subexpr = fmap Paren (parens lexer parseExpr)
          <|>  parseConst constantsList
          <|>  parseQuant quantifiersList
          <|>  parseExprVar parseVar
          <|>  parseFunc
          <|>  parseSugarExpr parseExpr
                            
-- Parseo de Constantes definidas en la teoria

-- Vamos juntando las opciones de parseo de acuerdo a cada constante en la lista.
-- En el caso en que la lista es vacia, la opcion es un error
parseConst :: [Constant] -> Parser PreExpr
parseConst = foldr
                (\ c ->
                (<|>) (reserved lexer (unpack $ conRepr c) >> return (Con c)))
                (fail "Parser error: Expresion mal formada")
                    
   
   
-- Parseo de Cuantificadores definidos en la teoria
parseQuant :: [Quantifier] -> Parser PreExpr
parseQuant = foldr
                (\ q ->
                    (<|>) (try $
                            reserved lexer quantInit >>
                            reserved lexer (unpack $ quantRepr q) >>
                            (parseVar <?> "Cuantificador sin variable") >>=
                            \v -> reserved lexer quantSep >> parseExpr >>=
                            \r -> reserved lexer quantSep >> parseExpr >>=
                            \t -> reserved lexer quantEnd >> return (Quant q v r t)))
                (fail "Parse error: Expresi\243n mal formada")



-- Parseo de expresiones variable
parseExprVar :: Parser Variable -> Parser PreExpr
parseExprVar pars_v = pars_v >>= \v -> return (Var v)

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

parseSugarExpr :: Parser PreExpr -> Parser PreExpr
parseSugarExpr = undefined

-- Funcion principal de parseo
parser :: String -> Either ParseError PreExpr
parser = parse parseExpr ""


-- Expresiones de prueba:
-- (F@(succ 0) + x) ▹ [] ⇒ True
-- 〈 ∃ x : (G@(# []) + x) ▹ [] ⇒ True : p ⇒ q 〉

