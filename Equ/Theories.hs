-- | En este m&#243;dulo se re-exportan las definiciones sintácticas
-- de cada teoría y las reglas de reescritura de expresiones que
-- incluyen elementos sintácticos definidos en esa teoría.

module Equ.Theories 
    ( -- * Teor&#237;as.
      operatorsList
    , constantsList
    , quantifiersList
    , axiomList
    , L.listRules
    , relationList
    , relationToOperator
    , createTheorem
    )
    where

import qualified Equ.Theories.Arith as A
import qualified Equ.Theories.List as L
import qualified Equ.Theories.FOL as F
import Equ.Rule
import Equ.Syntax (Operator,Constant,Quantifier)
import Equ.Proof
import Equ.Expr
import Equ.PreExpr

import Data.Text hiding (head)
import Data.Either(rights)

operatorsList :: [Operator]
operatorsList = A.theoryOperatorsList ++ L.theoryOperatorsList ++ F.theoryOperatorsList

constantsList :: [Constant]
constantsList = A.theoryConstantsList ++ L.theoryConstantsList ++ F.theoryConstantsList

quantifiersList :: [Quantifier]
quantifiersList = A.theoryQuantifiersList ++ L.theoryQuantifiersList ++ F.theoryQuantifiersList

relationList :: [Relation]
relationList = [relEq,relEquiv,relImpl,relCons]

axiomList :: [Axiom]
axiomList = F.theoryAxiomList

relationToOperator :: Relation -> Operator
relationToOperator relation | relation == relEq = F.folEqual
                            | relation == relEquiv = F.folEquiv
                            | relation == relImpl = F.folImpl
                            | relation == relCons = F.folConseq



-- DUDA: VER SI ESTAS FUNCIONES QUE SIGUEN DEBEN IR EN ESTE MODULO O EN OTRO.
-- LAS QUISE PONER EN Equ.Proof PERO TENEMOS PROBLEMAS CON LOS IMPORTS


-- Funcion que dada una prueba y un nombre, crea un teorema:
-- Asume que la prueba tiene expresión inicial, final y relacion.

createTheorem :: Text -> Proof -> Theorem
createTheorem th_name proof = Theorem {
      thName = th_name
    , thExpr = Expr $ BinOp (relationToOperator (fromRight $ getRel proof))
                                   exp1
                                   exp2
    , thRel = fromRight $ getRel proof
    , thProof = proof
    , thRules = createRules exp1 exp2 (fromRight $ getRel proof)
    }
    
    where exp1 = (toExpr $ fromRight $ getStart proof)
          exp2 = (toExpr $ fromRight $ getEnd proof)
     
createRules :: PreExpr -> PreExpr -> Relation -> [Rule]
createRules pe1 pe2 relation = [r1,r2,r3]
    where r1= Rule {
              lhs = Expr pe1
            , rhs = Expr pe2
            , rel = relation
            , name = pack ""
            , desc = pack ""
          }
          r2= Rule {
              lhs = expr
            , rhs = F.true
            , rel = relEquiv
            , name = pack ""
            , desc = pack ""
          }
          r3= Rule {
              lhs = F.true
            , rhs = expr
            , rel = relEquiv
            , name = pack ""
            , desc = pack ""
          }
          
          expr = Expr $ BinOp (relationToOperator relation)
                                   pe1
                                   pe2

fromRight = head . rights . return      