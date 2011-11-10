-- | Este módulo importa las distintas teorías y expone los
-- constructores necesarios de cada una.
module Equ.Theories 
    ( -- * Teorías.
      operatorsList
    , constantsList
    , quantifiersList
    --, axiomList
    , L.listRules
    , relationList
    )
    where

import qualified Equ.Theories.Arith as A
import qualified Equ.Theories.List as L
import qualified Equ.Theories.FOL as F
import Equ.Rule
import Equ.Syntax (Operator,Constant,Quantifier)

operatorsList :: [Operator]
operatorsList = A.theoryOperatorsList ++ L.theoryOperatorsList ++ F.theoryOperatorsList

constantsList :: [Constant]
constantsList = A.theoryConstantsList ++ L.theoryConstantsList ++ F.theoryConstantsList

quantifiersList :: [Quantifier]
quantifiersList = A.theoryQuantifiersList ++ L.theoryQuantifiersList ++ F.theoryQuantifiersList

relationList :: [Relation]
relationList = [relEq,relEquiv,relImpl,relCons]

-- axiomList :: [Axiom]
-- axiomList = F.theoryAxiomList