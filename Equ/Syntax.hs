-- | En este módulo definimos los posibles valores de las hojas de
-- pre-expresiones y expresiones. El campo correspondiente al tipo
-- tiene dos significados diferentes: cuando se está en una pre-expresión
-- corresponde a información dada por el usuario; cuando se está en
-- las expresiones es el tipo definido por la teoría correspondiente
-- a donde se definió el término en cuestión o el tipo inferido (por 
-- ejemplo en variables) por el type-checker.
module Equ.Syntax where

import Data.Text
import Equ.Types

data Variable = Variable {
      varName :: Text
    , varTy   :: Type
    }

data Constant = Constant {
      conName :: Text
    , conTy   :: Type
    }

data Operator = Operator {
      opName :: Text               
    , opTy   :: Type
    } 

data Func = Func {
      funcName :: Text
    , funcTy   :: Type
    }

data Quantifier = Quantifier {
      quantName :: Text
    , quantTy   :: Type
    }

-- | Un hueco corresponde a una expresión o pre-expresión ausente
-- pero en el contexto de otra expresión más grande. Esta es una
-- manera de formalizar la idea de meta-variable. La necesidad de
-- huecos se puede ver al querer reconstruir la expresión original
-- luego de aplicar una regla, pero sin el resultado de la regla.
data Hole = Hole {
      holeTy :: Type
    }