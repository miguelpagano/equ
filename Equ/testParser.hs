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

import Equ.Theories.FOL
import Equ.Syntax
import Equ.PreExpr
import Equ.Types

{- operadores y constantes de la teoria FOL 
   Tendriamos que tener una funcion que dada una teoria devuelva los operadores,
   las constantes, etc -}
folOperators :: [Operator]
folOperators = [folEquiv,folDiscrep,folAnd,folOr,folImpl,folNeg,folConseq]

folConst :: [Constant]
folConst = [folTrue,folFalse]

folQuants :: [Quantifier]
folQuants = [folForall,folExist]

-- Para los cuantificadores:
quantInit = "〈"
quantEnd = "〉"
quantSep = ":"

lexer :: TokenParser ()
lexer = makeTokenParser $
            emptyDef { reservedOpNames = map (unpack . opRepr) folOperators
                     , reservedNames = [quantInit,quantEnd,quantSep] ++ 
                       (map (unpack . conRepr) folConst) ++
                       (map (unpack .quantRepr) folQuants)
                     , identStart  = letter <|> char '_'
                     , identLetter = alphaNum <|> char '_'
            }

parseExpr :: Parser PreExpr
parseExpr = ParsecExpr.buildExpressionParser operatorTable subexpr <?> "Parser error: Expresión mal formada"


-- Construimos la table que se le pasa a buildExpressionParser:

operatorTable :: ParsecExpr.OperatorTable String () Identity PreExpr
operatorTable = makeTable folOperators

makeTable :: [Operator] -> ParsecExpr.OperatorTable String () Identity PreExpr
makeTable l = map makeSubList (group $ reverse $ sort l)

makeSubList :: [Operator] -> [ParsecExpr.Operator String () Identity PreExpr]
makeSubList [] = []
makeSubList (op:ops) =  case op of
                             Operator {opNotationTy=NPrefix} ->
                                (ParsecExpr.Prefix ((reservedOp lexer) (unpack $ opRepr op) >> return (UnOp op))) : makeSubList ops
                             Operator {opNotationTy=NPostfix} ->
                                (ParsecExpr.Postfix ((reservedOp lexer) (unpack $ opRepr op) >> return (UnOp op))) : makeSubList ops
                             otherwise ->
                                (ParsecExpr.Infix ((reservedOp lexer) (unpack $ opRepr op) >> return (BinOp op)) (convertAssoc $ opAssoc op)) : makeSubList ops

convertAssoc :: Assoc -> ParsecExpr.Assoc
convertAssoc None = ParsecExpr.AssocNone
convertAssoc ALeft = ParsecExpr.AssocLeft
convertAssoc ARight = ParsecExpr.AssocRight

-- Parseamos las subexpresiones
subexpr :: Parser PreExpr
subexpr = ((parens lexer) parseExpr >>= return . Paren)
          <|>  parseConst folConst
          <|>  parseQuant folQuants
          <|>  parseExprVar parseVar
          <|>  parseFunc
                            
-- Parseo de Constantes definidas en la teoria                            
parseConst :: [Constant] -> Parser PreExpr
parseConst (c:cs) = ((reserved lexer) (unpack $ conRepr c) >> return (Con c)) <|> parseConst cs
parseConst [] = fail "Parser error: Expresión mal formada"
   
   
-- Parseo de Cuantificadores definidos en la teoria
parseQuant :: [Quantifier] -> Parser PreExpr
parseQuant (q:qs) = (try $
                        (reserved lexer) (quantInit) >>
                        (reserved lexer) (unpack $ quantRepr q) >> (parseVar <?> "Cuantificador sin variable") >>=
                         \v -> (reserved lexer) quantSep >> parseExpr >>=
                         \r -> (reserved lexer) quantSep >> parseExpr >>=
                         \t -> (reserved lexer) quantEnd >> return (Quant q v r t))
                     <|> parseQuant qs
parseQuant [] = fail "Parse error: Expresión mal formada"


-- Parseo de expresiones variable
parseExprVar :: Parser Variable -> Parser PreExpr
parseExprVar pars_v = pars_v >>= \v -> return (Var v)

-- Esta funcion parsea una variable. Nos fijamos que empiece con minuscula para distinguirla
-- de las funciones que empiezan con mayuscula. La idea es tomada de Yahc.
parseVar :: Parser Variable
parseVar = try $ (identifier lexer) >>= \s -> if (not . null) s && (isLower . head) s
                                           then return (Variable { varName= pack s
                                                                 , varTy= TyUnknown
                                                                 }
                                                       )
                                           else parserZero

-- Parseo de funciones
parseFunc :: Parser PreExpr
parseFunc = (identifier lexer) >>= \s -> if (not . null) s && (isUpper . head) s
                                           then return (Fun (Func { funcName= pack s
                                                                  , funcTy= TyUnknown
                                                                   })
                                                       )
                                           else fail "Error parseando funcion"


-- Funcion principal de parseo
parser :: String -> Either ParseError PreExpr
parser s = parse parseExpr "" s

