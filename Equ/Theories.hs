-- | Este módulo importa las distintas teorías y expone los
-- constructores necesarios de cada una.
module Equ.Theories 
    ( -- * Teorías.
      operatorsList
    , constantsList
    , quantifiersList
    , L.listRules
    )
    where

import qualified Equ.Theories.Arith as A
import qualified Equ.Theories.List as L
import qualified Equ.Theories.FOL as F
import Equ.Syntax (Operator,Constant,Quantifier)

operatorsList :: [Operator]
operatorsList = A.theoryOperatorsList ++ L.theoryOperatorsList ++ F.theoryOperatorsList

constantsList :: [Constant]
constantsList = A.theoryConstantsList ++ L.theoryConstantsList ++ F.theoryConstantsList

quantifiersList :: [Quantifier]
quantifiersList = A.theoryQuantifiersList ++ L.theoryQuantifiersList ++ F.theoryQuantifiersList
