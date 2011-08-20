-- | Este modulo es el parser de expresiones de tipos. 

module Equ.Parser.Types (listAtomTy, parseTy) where

import Text.Parsec
import Text.Parsec.Token
import Text.Parsec.Language
import Text.Parsec.String
import qualified Text.Parsec.Expr as PE

import Control.Monad.Identity
import Control.Applicative ((<$>),(<$))
import Equ.Types



-- | Para definir la función anterior podemos necesitar definir 
-- esta función para poder parsear los tipos que el usuario quiera
-- asignar a los diferentes constituyentes de pre-expresiones.
-- parserTy :: Text -> Either ParseError Type
-- parserTy = undefined

type ParserTypeTable = PE.OperatorTable String () Identity Type

-- Numeros
num :: String
num = "Num"

-- Enteros
int :: String
int = "Int"

-- Naturales
nat :: String
nat = "Nat"

-- Booleanos.
bool :: String
bool = "Bool"

-- Operador de funcion.
opFun :: String
opFun = ":->"

-- | Nombre de los tipos atomicos.
listAtomTy :: [String]
listAtomTy = [num, int, nat, bool]

-- | Nombre para indicar tipo desconocido.
typeUnknown :: String
typeUnknown = "¿Type?"

lexerTy :: TokenParser ()
lexerTy = makeTokenParser $
            emptyDef { reservedOpNames = [opFun]
                     , reservedNames = typeUnknown : listAtomTy
                     , identStart  = letter <|> char '_'
                     , identLetter = alphaNum <|> char '_'
                     }

operatorTypeTable :: ParserTypeTable
operatorTypeTable = [[PE.Infix (reservedOp lexerTy opFun >> return (:->)) PE.AssocRight]]

typeSubExpr :: Parser Type
typeSubExpr =  parseUnknown
           <|> parseTyVar
           <|> parseTyList
           <|> parseTyAtom

-- Parseo de tipos.
parseType :: Parser Type
parseType = PE.buildExpressionParser operatorTypeTable typeSubExpr 
               <?> "Parser error: Expresión mal formada"

-- | Parser para los tipos atomicos.
parseAtomTy :: Parser AtomTy
parseAtomTy = foldr ((<|>) . uncurry patom) parserZero atoms 
    where atoms = [(num,ATyNum),(int,ATyInt),(nat,ATyNat),(bool,ATyBool)]
          patom iden ty = ty <$ (try $ reserved lexerTy iden)

-- | Parser para el tipo Unknown.
parseUnknown :: Parser Type
parseUnknown = TyUnknown <$ (try $ reserved lexerTy typeUnknown)

-- | Parser para el tipo variable.
parseTyVar :: Parser Type
parseTyVar = try $ lower >>= \l -> many letter >>= \t -> return (tyVar (l:t))

-- | Parser para el tipo lista.
parseTyList :: Parser Type
parseTyList = TyList <$> brackets lexerTy parseType

-- | Parser para el tipo de tipos atomicos.
parseTyAtom :: Parser Type
parseTyAtom = TyAtom <$> try parseAtomTy

-- | Funcion principal de parseo desde string.
parseTyFromString :: String -> Either ParseError Type
parseTyFromString = parse parseType ""

-- | Parser de tipos.
parseTy :: String -> Type
parseTy = either showError showType . parseTyFromString

-- | Imprimimos Types usando que es instancia de show.
showType :: a -> a
showType = id

-- Expresiones de prueba:
-- (F@(succ 0) + x) ▹ [] ⇒ True
-- 〈∃ x : (G@(# []) + x) ▹ [] ⇒ True : p ⇒ q〉

-- Imprimimos el error con version Exception de haskell.
showError :: Show a => a -> b
showError = error . show
