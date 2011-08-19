-- | En este módulo definimos los posibles valores de las hojas de
-- pre-expresiones y expresiones. El campo correspondiente al tipo
-- tiene dos significados diferentes: cuando se está en una pre-expresión
-- corresponde a información dada por el usuario; cuando se está en
-- las expresiones es el tipo definido por la teoría correspondiente
-- a donde se definió el término en cuestión o el tipo inferido (por 
-- ejemplo en variables) por el type-checker.
module Equ.Syntax where

import Equ.Types
import Equ.Theories.AbsName
import Control.Applicative((<$>),(<*>))
import Test.QuickCheck(Arbitrary, arbitrary, elements)

import Data.Text hiding (null)

type VarName = Text
type FuncName = Text
type HoleInfo = Text

data Variable = Variable {
      varName :: VarName
    , varTy   :: Type
    }

instance Eq Variable where 
    v == v' = tRepr v == tRepr v'

data Constant = Constant {
      conRepr :: Text
    , conName :: ConName
    , conTy   :: Type
    }
    deriving Eq
    
data Operator = Operator {
      opRepr :: Text   
    , opName :: OpName
    , opTy   :: Type
    , opAssoc :: Assoc
    , opNotationTy :: NotationType
    , opPrec :: Int
    } 
    deriving Eq
    
instance Ord Operator where
    compare a b = compare (opPrec a) (opPrec b) 
    
instance Ord Variable where
    compare v v' = compare (tRepr v) (tRepr v')
    
data Func = Func {
      funcName :: FuncName
    , funcTy   :: Type
    }
    deriving Eq

data Assoc = None | ALeft | ARight
    deriving Eq

data NotationType = NInfix | NPrefix | NPostfix
    deriving Eq

-- En el tipo de los cuantificadores, en general se tendrá:
-- tipo1 :-> tipo2, donde tipo1 es el tipo de la variable cuantificada
-- y tipo2 es el tipo del termino y consecuentemente de toda la expresion.
data Quantifier = Quantifier {
      quantRepr :: Text
    , quantName :: QuantName
    , quantTy   :: Type
    }
    deriving Eq

-- | Un hueco corresponde a una expresión o pre-expresión ausente
-- pero en el contexto de otra expresión más grande. Esta es una
-- manera de formalizar la idea de meta-variable. La necesidad de
-- huecos se puede ver al querer reconstruir la expresión original
-- luego de aplicar una regla, pero sin el resultado de la regla.
data Hole = Hole {
      holeTy :: Type
    , info :: HoleInfo
    }
    deriving Eq

hole :: HoleInfo -> Hole
hole i = Hole {holeTy = TyUnknown
              , info = i
              }
  
var :: String -> Type -> Variable
var s t = Variable { varName = pack s
                   , varTy = t
                   }   
    
-- | La clase syntax abstrae la informacion común de los diferenctes 
--  constituyentes de los árboles sintácticos. Como información común
--  tenemos nombre y tipo.
--  Definicion completa minima: tName y tType.
class Syntactic t where
    tRepr :: t -> Text
    tType :: t -> Type
    
-- | Instancia de syntax para el tipo Varible.
instance Syntactic Variable where
    tRepr = varName
    tType = varTy
    
-- | Instancia de syntax para el tipo Constant.
instance Syntactic Constant where
    tRepr = conRepr
    tType = conTy

-- | Instancia de syntax para el tipo Operator.
instance Syntactic Operator where
    tRepr = opRepr
    tType = opTy

-- | Instancia de syntax para el tipo Function.
instance Syntactic Func where
    tRepr = funcName
    tType = funcTy
    
-- | Instancia de syntax para el tipo Quantifier.
instance Syntactic Quantifier where
    tRepr = quantRepr
    tType = quantTy

-- | Instancia de syntax para el tipo Hole.
instance Syntactic Hole where  
    tRepr _ = pack ""
    tType = holeTy

-- | PrettyPrint para variables. 
instance Show Variable where
    show = unpack . tRepr

-- | PrettyPrint para constantes. 
instance Show Constant where
    show = unpack . tRepr

-- | PrettyPrint para operadores. 
instance Show Operator where
    show = unpack . tRepr

-- | PrettyPrint para funciones. 
instance Show Func where
    show = unpack . tRepr

-- | PrettyPrint para cuantificadores. 
instance Show Quantifier where
    show = unpack . tRepr

-- | PrettyPrint para huecos. 
instance Show Hole where
    show s = let i = unpack $ info s in
                if null i
                then "_"
                else "holeWithInfo: " ++ ((unpack . info) s)

-- | Instancia arbitrary para las variables.
instance Arbitrary Variable where
    arbitrary = Variable <$> arbitrary <*> arbitrary

-- | Instancia arbitrary para constantes.
instance Arbitrary Constant where
    arbitrary = Constant <$> arbitrary <*> arbitrary <*> arbitrary
    
-- | Instancia arbitrary para los operadores.
instance Arbitrary Operator where
    arbitrary = Operator <$> arbitrary <*> 
                arbitrary <*> arbitrary <*> 
                arbitrary <*> arbitrary <*> arbitrary

-- | Instancia arbitrary para las funciones.
instance Arbitrary Func where
    arbitrary = Func <$> arbitrary <*> arbitrary
        
-- | Instancia arbitrary para los cuantificadores.
instance Arbitrary Quantifier where
    arbitrary = Quantifier <$> arbitrary <*> arbitrary <*> arbitrary

-- | Instancia arbitrary para los huecos.
instance Arbitrary Hole where
    arbitrary = Hole <$> arbitrary <*> arbitrary 

-- | Instancia arbitrary para las asociaciones.
instance Arbitrary Assoc where
    arbitrary = elements [ None , ALeft , ARight ]

-- | Instancia arbitrary para el tipo de notacion.
instance Arbitrary NotationType where
    arbitrary = elements [ NInfix , NPrefix , NPostfix ]
