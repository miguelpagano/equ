-- | Este m&#243;dulo importa las distintas teor&#237;as y expone los
-- constructores necesarios de cada una.
module Equ.Theories 
    ( -- * Teor&#237;as.
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
