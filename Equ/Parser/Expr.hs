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

module Equ.Parser.Expr
    (-- * Caracteres especiales comunes a todas las teorías
      LangDef (..)
    , Parser'
    , equLang
    -- * Funciones principales de parseo
    , parseFromString
    , parsePreExpr
    , parser
    , parserVar
    , VarTy
    , initPExprState
    , PExprState
    , ParenFlag (..)
    )
    where

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


import Equ.Syntax
import Equ.PreExpr 
import Equ.Types
import Equ.Theories (operatorsList,constantsList,quantifiersList)
import Equ.Theories.List(listApp, listEmpty)
import Equ.Theories.Arith(intToCon)
import Equ.Parser.Types(listAtomTy, parseTyFromString)

data PError = UnOpNotApplied Operator 
            | BinOpNotApplied Operator

type VarTy = (Int,Map (Either VarName FuncName) Type)

type PExprState = (VarTy,ParenFlag)

data ParenFlag = UseParen | UnusedParen

type ParserTable = PE.OperatorTable String PExprState Identity PreExpr
type Parser' a = ParsecT String PExprState Identity a
type ParserOper = PE.Operator String PExprState Identity PreExpr

-- | Configuración del parser.
data LangDef = LangDef {
      quantInit :: String    -- ^ Inicio de una cuantificaci&#243;n.
    , quantEnd :: String     -- ^ Final de una cuantificaci&#243;n.
    , quantSep :: String     -- ^ Separador de la cuantificaci&#243;n.
    , opApp :: String        -- ^ Operador para la aplicaci&#243;n.
    , holeInfoInit :: String -- ^ Inicio de información en un hueco.
    , holeInfoEnd :: String  -- ^ Fin de información en un hueco.
    , opHole :: String       -- ^ Marca de un hueco.
    , opUnCurriedApp :: String -- ^ Operador para aplicación uncurrificada.
    }

equLang :: LangDef
equLang = LangDef { 
            quantInit = "〈" 
          , quantEnd = "〉" 
          , quantSep = ":" 
          , opApp = "@"
          , holeInfoInit = "{"
          , holeInfoEnd = "}"
          , opHole = "?"
          , opUnCurriedApp = "%"
          }

-- | Representantes de los operadores. (Salvo para aplicación)
rOpNames :: [String]
rOpNames = map ($ equLang) [opApp, opHole, opUnCurriedApp] 
        ++ map (unpack . opRepr) operatorsList

-- | Representantes de las constantes y cuantificadores.
-- Adem&#225;s de los caracteres para representar expresiones cuantificadas.
rNames :: [String]
rNames = (map ($ equLang) [quantInit,quantEnd,quantSep])
         ++ map (unpack . conRepr) constantsList
         ++ map (unpack . quantRepr) quantifiersList
         ++ listAtomTy

-- Para lexical analisys.
lexer' :: TokenParser PExprState
lexer' = makeTokenParser $
            emptyDef { reservedOpNames = rOpNames
                     , reservedNames = rNames
                     , identStart  = letter
                     , identLetter = alphaNum <|> char '_'
                     }

lexer = lexer' { whiteSpace = oneOf " \t" >> return ()}

-- Parser principal de preExpresiones.
parsePreExpr :: Parser' PreExpr
parsePreExpr = getState >>= \(_,flag) ->
                PE.buildExpressionParser operatorTable (subexpr flag)
               <?> "Parser error: Expresi&#243;n mal formada"

-- Construimos la table que se le pasa a buildExpressionParser:
-- Primero agregamos el operador aplicaci&#243;n, que precede a cualquier otro
operatorTable :: ParserTable
operatorTable = [parserApp] : makeTable operatorsList
    where parserApp = PE.Infix (App <$ reservedOp lexer (opApp equLang)) PE.AssocLeft

-- Genera un ParserTable de una lista de operadores.
makeTable :: [Operator] -> ParserTable
makeTable = map makeSubList . group . reverse . sort 

-- Genera un ParserOper de un operador.
makeOp :: Operator -> [ParserOper]
makeOp op = map mkop $ opRepr op : opGlyphs op
    where mkop s = case opNotationTy op of 
                     NInfix   -> PE.Infix   (BinOp op <$ parseOp s) assoc
                     NPrefix  -> PE.Prefix  $ UnOp op <$ parseOp s
                     NPostfix -> PE.Postfix $ UnOp op <$ parseOp s
          parseOp = reservedOp lexer . unpack
          assoc = convertAssoc . opAssoc $ op

makeSubList :: [Operator] -> [ParserOper]
makeSubList = concatMap makeOp

-- Convierte el nuestro tipo de asociaci&#243;n al tipo de asociaci&#243;n de parsec.
convertAssoc :: Assoc -> PE.Assoc
convertAssoc None = PE.AssocNone
convertAssoc ALeft = PE.AssocLeft
convertAssoc ARight = PE.AssocRight

-- Parseamos las subexpresiones
-- Una expresion puede ser una expresion con parentesis, una constante, una expresion cuantificada,
-- una variable, una funci&#243;n o una expresion que viene desde un parseo por syntactic sugar
subexpr :: ParenFlag -> Parser' PreExpr
subexpr flag = parseParen <$> parens lexer parsePreExpr
            <|> Con <$> parseConst
            <|> parseQuant 
            <|> parseIf
            <|> parseCase
            <|> Var <$> parseVar
            <|> parseHole
--            <|> parseSugarPreExpr parsePreExpr                                
    where
        parseParen :: (PreExpr -> PreExpr)
        parseParen = case flag of
                        UseParen -> Paren
                        UnusedParen -> id
                            
-- Parseo de Constantes definidas en la teoria
-- Vamos juntando las opciones de parseo de acuerdo a cada constante en la lista.
-- En el caso en que la lista es vacia, la opcion es un error
parseConst :: Parser' Constant
parseConst = foldr ((<|>) . pConst) (fail "Constante") constantsList
    where pConst c = c <$ (reserved lexer . unpack . conRepr) c
   
-- Parseo de Cuantificadores definidos en la teoria
parseQuant ::  Parser' PreExpr
parseQuant = foldr ((<|>) . pQuan) (fail "Cuantificador") quantifiersList

-- Funci&#243;n auxiliar para el parseo de quantificadores.
pQuan :: Quantifier -> Parser' PreExpr
pQuan q = try $ symbol lexer (quantInit equLang) >>
          (symbol lexer . unpack . quantRepr) q >>
          (parseVar <?> "Cuantificador sin variable") >>= 
          \v -> symbol lexer (quantSep equLang) >> parsePreExpr >>=
          \r -> symbol lexer (quantSep equLang) >> parsePreExpr >>=
          \t -> symbol lexer (quantEnd equLang) >> return (Quant q v r t)

-- Parseo de huecos.
parseHole :: Parser' PreExpr
parseHole = PrExHole . hole . pack <$> 
                (try $ reserved lexer (opHole equLang) >> braces lexer parseInfo)
            <|> fail "Hueco"

parseApp :: Parser' PreExpr
parseApp = parsePreExpr >>= \e -> whiteSpace lexer' >> App <$> return e <*> parsePreExpr 

-- Parseo de la informacion de un hueco.
parseInfo :: Parser' String
parseInfo = many $ letter <|> oneOf " \t"

-- Parseo de if-then-else
parseIf :: Parser' PreExpr
parseIf = reserved lexer "if" >>
          parsePreExpr >>= \ cond ->
          reserved lexer "then" >>
          parsePreExpr >>= \ branchT ->
          reserved lexer "else" >>
          parsePreExpr >>= \ branchF ->
          reserved lexer "fi" >>
          return (If cond branchT branchF)
          
parseCase :: Parser' PreExpr
parseCase = reserved lexer "case" >>
            parsePreExpr >>= \ expr ->
            reserved lexer "of" >>
            manyTill1 parseCases (reserved lexer "end") >>= \ cases ->
            return (Case expr cases)
    where
        manyTill1 :: Parser' a -> Parser' end -> Parser'[a]
        manyTill1 p till = p >>= \ x ->
                           manyTill p till >>= \ xs ->
                           return (x:xs)
        parseCases :: Parser' (PreExpr,PreExpr)
        parseCases = parsePreExpr >>= \ c ->
                     reserved lexer "->" >>
                     parsePreExpr >>= \ ce ->
                     return (c,ce)

-- Esta funcion parsea una variable. Nos fijamos que empiece con
-- minuscula para distinguirla de las funciones (que empiezan con
-- mayuscula). 
parseVar :: Parser' Variable
parseVar = try $ lexeme lexer ((:) <$> lower <*> many alphaNum) >>= 
           \v -> return (var (pack v) TyUnknown)


-- //////// Parser de syntax sugar ////////

-- Parseo de expresiones azucaradas.
parseSugarPreExpr :: Parser' PreExpr -> Parser' PreExpr
parseSugarPreExpr p =  parseSugarApp p <|> parseSugarList p <|>  parseIntPreExpr

-- | Parseo de la lista escrita con syntax sugar.
sugarList :: Parser' PreExpr -> Parser' PreExpr
sugarList p = foldr (BinOp listApp) (Con listEmpty) <$> (commaSep lexer p)

-- | Parseo de la lista escrita con syntax sugar.
parseSugarList :: Parser' PreExpr -> Parser' PreExpr
parseSugarList = brackets lexer . sugarList

-- | Parseo de una funci&#243;n aplicada: f(a,b). Por ahora sólo se
-- puede aplicar un símbolo de función en el lado izquierdo de la
-- aplicación; el problema con una expresión completa es que el lado
-- izquierdo puede ser en sí mismo una aplicación.
parseSugarApp :: Parser' PreExpr -> Parser' PreExpr
parseSugarApp p = p >>= \func ->
                  reservedOp lexer (opUnCurriedApp equLang) >>
                  parens lexer (commaSep lexer p) >>= \args ->
                  (return . foldl1 App) (func:args)

-- | Parseo de enteros.
parseInt :: Parser' Int
parseInt = fromInteger <$> natural lexer <?> fail "Numero"

-- | Parseo de enteros preExpr.
parseIntPreExpr :: Parser' PreExpr
parseIntPreExpr = intToCon <$> parseInt

-- //////// Parser de syntax sugar ////////

-- | Funcion principal de parseo desde string.
parseFromString' :: ParenFlag -> String -> Either ParseError PreExpr
parseFromString' flag = runParser parsePreExpr (initPExprState flag) "TEST"

parseFromString :: String -> Either ParseError PreExpr
parseFromString s = case parseFromString' UseParen s of
                         Left er -> Left er
                         Right pe -> Right $ unParen pe

parseFromStringUnusedP :: String -> Either ParseError PreExpr
parseFromStringUnusedP s = case parseFromString' UnusedParen s of
                         Left er -> Left er
                         Right pe -> Right $ unParen pe


initPExprState :: ParenFlag -> PExprState
initPExprState flag = ((0,M.empty),flag)
-- | Gramatica de parseo.
--
-- @
-- \<PreExpr\> ::= \<Atoms\>
--           | \<UnOp\>
--           | \<BinOp\>
--           | \<App\>
--           | \<Quant\>
--           | \<Parent\>
--           | if <PreExpr> then <PreExpr> else <PreExpr> fi
-- 
-- \<Var\> ::= {a, b, c, ... , z}*
-- \<Func\> ::= {A, B, C, ... , Z}*
-- \<Const\> ::= True | False | [] | 0
-- \<String\> ::= {a, b, c, ... , z, A, B, C, ... , Z}*
-- 
-- \<Atoms\> ::= \<Var\>
--          |  \<Func\>
--          |  \<Const\>
--          |  ?{\<String\>}
--
-- \<UnOp\> ::= &#172; \<PreExpr\>
--         |  # \<PreExpr\>
--         |  Succ \<PreExpr\>
--
-- \<BinOp \> ::= \<PreExpr> &#8743; \<PreExpr\>
--           |  \<PreExpr\> &#8744; \<PreExpr\>
--           |  \<PreExpr\> &#8658; \<PreExpr\>
--           |  \<PreExpr\> &#8656; \<PreExpr\>
--           |  \<PreExpr\> &#8801; \<PreExpr\>
--           |  \<PreExpr\> /&#8801; \<PreExpr\>
--           |  \<PreExpr\> = \<PreExpr\>
--           |  \<PreExpr\> &#9657; \<PreExpr\>
--           |  \<PreExpr\> &#8593; \<PreExpr\>
--           |  \<PreExpr\> &#8595; \<PreExpr\>
--           |  \<PreExpr\> . \<PreExpr\>
--           |  \<PreExpr\> ++ \<PreExpr\>
--           |  \<PreExpr\> + \<PreExpr\>
--           |  \<PreExpr\> * \<PreExpr\>
-- 
-- \<App\> ::= \<PreExpr\> \@ \<PreExpr\>
-- 
-- \<Quant\> ::= &#12296;&#8704;\<Var\> : \<PreExpr\> : \<PreExpr\>&#12297;
--          |  &#12296;&#8707;\<Var\> : \<PreExpr\> : \<PreExpr\>&#12297;
-- 
-- \<Parent\> ::= ( \<PreExpr\> )
-- @
parser :: String -> PreExpr
parser = either showError showPreExpr . parseFromString

parserVar :: ParenFlag -> String -> Either ParseError Variable
parserVar flag = runParser parseVar ((0,M.empty),flag) "TEST" 

-- Imprimimos el error con version Exception de haskell.
showError :: Show a => a -> b
showError = error . show

-- Imprimimos la preExpresion, usando que tenemos definido la instancia show.
showPreExpr :: a -> a
showPreExpr = id
