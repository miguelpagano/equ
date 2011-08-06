-- parser de prueba para parsear expresiones en la teoria FOL:

import Text.Parsec
import Text.Parsec.Token
import Text.Parsec.Language
import Text.Parsec.String
import qualified Text.Parsec.Expr as ParsecExpr
import Data.Text (pack,unpack)
import Data.List
import Control.Monad.Identity

import Equ.Theories.FOL
import Equ.Syntax
import Equ.PreExpr

{- operadores y constantes de la teoria FOL 
   Tendriamos que tener una funcion que dada una teoria devuelva los operadores,
   las constantes, etc -}
folOperators :: [Operator]
folOperators = [folEquiv,folDiscrep,folAnd,folOr,folImpl,folNeg,folConseq]

folConst :: [Constant]
folConst = [folTrue,folFalse]


lexer :: TokenParser ()
lexer = makeTokenParser $
            emptyDef { reservedOpNames = map (unpack . opRepr) folOperators
                     , reservedNames = map (unpack . conRepr) folConst
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
subexpr = (parens lexer) parseExpr
          <|>  parseConst folConst
                            
                            
parseConst :: [Constant] -> Parser PreExpr
parseConst (c:cs) = ((reserved lexer) (unpack $ conRepr c) >> return (Con c)) <|> parseConst cs
parseConst [] = fail "Parser error: Expresion mal formada"
   
   
-- Funcion principal de parseo
parser :: String -> Either ParseError PreExpr
parser s = parse parseExpr "" s

