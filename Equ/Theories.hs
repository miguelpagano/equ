-- | Este módulo importa las distintas teorías y expone los
-- constructores necesarios de cada una.
module Equ.Theories 
    ( -- * Teorías.
     module Equ.Theories.List 
    )
    where

import qualified Equ.Theories.Arith as A
import qualified Equ.Theories.List as L
import qualified Equ.Theories.FOL as F

operatorsList = A.theoryOperatorsList ++ L.theoryOperatorsList ++ F.theoryOperatorsList
constantsList = A.theoryConstantsList ++ L.theoryConstantsList ++ F.theoryConstantsList
quantifiersList = A.theoryQuantifiersList ++ L.theoryQuantifiersList ++ F.theoryQuantifiersList
