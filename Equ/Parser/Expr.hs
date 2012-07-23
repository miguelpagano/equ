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
    , PExprState (..)
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


import System.IO.Unsafe

data PError = UnOpNotApplied Operator 
            | BinOpNotApplied Operator

type VarTy = (Int,Map (Either VarName FuncName) Type)

data PExprState = PExprState { peVarTy :: VarTy
                             , peParenFlag :: ParenFlag
                             }

data ParenFlag = UseParen | UnusedParen

type ParserTable = OperatorTable String PExprState Identity PreExpr
type Parser' a = ParsecT String PExprState Identity a
type ParserOper = POperator String PExprState Identity PreExpr
type ParserSide s u m a = ParsecT s u m a -> ParsecT s u m a

data POperator s u m a = Infix (ParsecT s u m ( a -> a -> a
                                              , ParserSide s u m a)
                                              ) PE.Assoc
                       | Prefix (ParsecT s u m (a -> a))
                       | Postfix (ParsecT s u m (a -> a))

type OperatorTable s u m a = [[POperator s u m a]]

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
rNames = map ($ equLang) [quantInit,quantEnd,quantSep]
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
                     --, opLetter = newline
                     }

lexer = lexer' { whiteSpace = oneOf " \t" >> return ()}

-- Parser principal de preExpresiones.
parsePreExpr :: Parser' PreExpr
parsePreExpr = getState >>= \st ->
               buildExprParser operatorTable (subexpr (peParenFlag st))
               <?> "Parser error: Expresi&#243;n mal formada"

-- Construimos la table que se le pasa a buildExpressionParser:
-- Primero agregamos el operador aplicaci&#243;n, que precede a cualquier otro
operatorTable :: ParserTable
operatorTable = [parserSugarApp, parserApp] : makeTable operatorsList
    where 
        parserApp = Infix ((App, id) <$ reservedOp lexer (opApp equLang)) PE.AssocLeft
        parserSugarApp = Infix ((App, parseArgs) <$ reservedOp lexer (opUnCurriedApp equLang)) PE.AssocLeft
        parseArgs p = foldl1 App <$> parens lexer (commaSep lexer p)

-- Genera un ParserTable de una lista de operadores.
makeTable :: [Operator] -> ParserTable
makeTable = map makeSubList . group . reverse . sort 

-- Genera un ParserOper de un operador.
makeOp :: Operator -> [ParserOper]
makeOp op = map mkop $ opRepr op : opGlyphs op
    where mkop s = case opNotationTy op of 
                     NInfix   -> Infix   ((BinOp op, id) <$ parseOp s) assoc
                     NPrefix  -> Prefix  $ UnOp op <$ parseOp s
                     NPostfix -> Postfix $ UnOp op <$ parseOp s
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
subexpr flag =  parseSugarPreExpr parsePreExpr
            <|> parseParen <$> parens lexer parsePreExpr
            <|> Con <$> parseConst
            <|> parseQuant
            <|> parseIf
            <|> parseCase
            <|> Var <$> parseVar
            <|> parseHole
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
pQuan q = try $ 
          symbol lexer (quantInit equLang) >>
          (symbol lexer . unpack . quantRepr) q >>
          (parseVar <?> "Cuantificador sin variable") >>= 
          \v -> symbol lexer (quantSep equLang) >> parsePreExpr >>=
          \r -> symbol lexer (quantSep equLang) >> parsePreExpr >>=
          \t -> symbol lexer (quantEnd equLang) >> return (Quant q v r t)

-- Parseo de huecos.
parseHole :: Parser' PreExpr
parseHole = PrExHole . hole . pack <$> 
                try (reserved lexer (opHole equLang) >> braces lexer parseInfo)
            <|> fail "Hueco"

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

-- Calcula el tipo de una variable o funcion
setType :: Either VarName FuncName -> PExprState -> (PExprState,Type)
setType name pest = 
            let stv = peVarTy pest 
                n = fst stv
                st = snd stv
            in
            if name `M.member` st
            then (pest {peVarTy = (n,st)}, st ! name)
            else (pest {peVarTy = (n+1, insert name (newvar n) st)}, newvar n)
    where newvar = tyVarInternal

-- Esta funcion parsea una variable. Nos fijamos que empiece con
-- minuscula para distinguirla de las funciones (que empiezan con
-- mayuscula). 
parseVar :: Parser' Variable
parseVar = try $ lexeme lexer ((:) <$> lower <*> many alphaNum) >>= 
           \v -> return (var (pack v) TyUnknown)

-- //////// Parser de syntax sugar ////////

-- Parseo de expresiones azucaradas.
parseSugarPreExpr :: Parser' PreExpr -> Parser' PreExpr
parseSugarPreExpr p = parseSugarList p <|> parseIntPreExpr

-- | Parseo de la lista escrita con syntax sugar.
sugarList :: Parser' PreExpr -> Parser' PreExpr
sugarList p = foldr (BinOp listApp) (Con listEmpty) <$> commaSep lexer p

-- | Parseo de la lista escrita con syntax sugar.
parseSugarList :: Parser' PreExpr -> Parser' PreExpr
parseSugarList = brackets lexer . sugarList

-- | Parseo de enteros.
parseInt :: Parser' Int
parseInt = fromInteger <$> natural lexer <?> fail "Numero"

-- | Parseo de enteros preExpr.
parseIntPreExpr :: Parser' PreExpr
parseIntPreExpr = intToCon <$> parseInt--parseInt >>= \e -> error (show $ intToCon e)
                 

-- //////// Parser de syntax sugar ////////

-- | Funcion principal de parseo desde string.
parseFromString' :: ParenFlag -> String -> Either ParseError PreExpr
parseFromString' flag = runParser parser (initPExprState flag) "TEST"
    where
        parser = parsePreExpr >>= \expr -> eof >> return expr

parseFromString :: String -> Either ParseError PreExpr
parseFromString s = case parseFromString' UseParen s of
                         Left er -> Left er
                         Right pe -> Right $ unParen pe

parseFromStringUnusedP :: String -> Either ParseError PreExpr
parseFromStringUnusedP s = case parseFromString' UnusedParen s of
                         Left er -> Left er
                         Right pe -> Right $ unParen pe

parseFromFilePreExpr :: FilePath -> IO ()
parseFromFilePreExpr fp = readFile fp >>= \s -> 
                        case parseFromString s of
                            Right ps -> print "-------" >> 
                                        print ps
                            Left err -> print err

initPExprState :: ParenFlag -> PExprState
initPExprState = PExprState (0,M.empty)
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
parserVar flag = runParser parseVar (initPExprState flag) "TEST" 

-- Imprimimos el error con version Exception de haskell.
showError :: Show a => a -> b
showError = error . show

-- Imprimimos la preExpresion, usando que tenemos definido la instancia show.
showPreExpr :: a -> a
showPreExpr = id


-- buildExprParser :: Stream s m t =>
--                    OperatorTable s u m a -> ParsecT s u m a -> ParsecT s u m a
buildExprParser operators simpleExpr = foldl makeParser simpleExpr operators
    where
        initOps = ([],[],[],[],[])
        makeParser term ops = 
            let 
            (rassoc,lassoc,nassoc,prefix,postfix) = foldr splitOp initOps ops

            rassocOp   = choice rassoc
            lassocOp   = choice lassoc
            nassocOp   = choice nassoc
            prefixOp   = choice prefix  <?> ""
            postfixOp  = choice postfix <?> ""

            ambigious assoc op = try $
                do{ op
                  ; fail ("ambiguous use of a " 
                         ++ assoc 
                         ++ " associative operator"
                         )
                  }

            ambigiousRight    = ambigious "right" rassocOp
            ambigiousLeft     = ambigious "left" lassocOp
            ambigiousNon      = ambigious "non" nassocOp

            termP = do{ pre  <- prefixP
                      ; x    <- term
                      ; post <- postfixP
                      ; return (post (pre x))
                      }

            postfixP   = postfixOp <|> return id

            prefixP    = prefixOp <|> return id

            rassocP x  = do{ (f,parseR) <- rassocOp
                           ; y  <- do{ z <- parseR (termP >>= rlnOps)
                                     ; rassocP1 z 
                                     }
                           ; return (f x y)
                           }
                          <|> ambigiousLeft
                          <|> ambigiousNon

            rassocP1 x = rassocP x  <|> return x

            lassocP x  = do{ (f,parseR) <- lassocOp
                           ; y <- parseR (termP >>= rlnOps)
                           ; lassocP1 (f x y)
                           }
                          <|> ambigiousRight
                          <|> ambigiousNon

            lassocP1 x = lassocP x <|> return x

            nassocP x = do { (f,parseR) <- nassocOp
                           ; y <- parseR (termP >>= rlnOps)
                           ; ambigiousRight <|> ambigiousLeft <|> 
                             ambigiousNon   <|> return (f x y)
                           }
            
            rlnOps x = rassocP x <|> lassocP x <|> nassocP x <|> return x
            
            in do { x <- termP
                  ; rlnOps x <?> "operator"
                  }

        splitOp (Infix op assoc) (rassoc,lassoc,nassoc,prefix,postfix)
            = case assoc of
                PE.AssocNone  -> (rassoc,lassoc,op:nassoc,prefix,postfix)
                PE.AssocLeft  -> (rassoc,op:lassoc,nassoc,prefix,postfix)
                PE.AssocRight -> (op:rassoc,lassoc,nassoc,prefix,postfix)

        splitOp (Prefix op) (rassoc,lassoc,nassoc,prefix,postfix)
            = (rassoc,lassoc,nassoc,op:prefix,postfix)

        splitOp (Postfix op) (rassoc,lassoc,nassoc,prefix,postfix)
            = (rassoc,lassoc,nassoc,prefix,op:postfix)
