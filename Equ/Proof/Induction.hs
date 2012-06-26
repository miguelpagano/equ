{-# Language OverloadedStrings #-}
module Equ.Proof.Induction (
    createIndHypothesis
    ) where

import Equ.Proof.Proof
import Equ.Theories.FOL
import qualified Equ.PreExpr as PE
import Equ.Syntax
import Equ.Types
import Equ.Expr
import Equ.TypeChecker(unifyTest)
import Equ.Theories(relToOp, createHypothesis)
import Equ.Rule(Relation)

import qualified Data.Map as Map
import Data.Text

-- | Dada la relacion de una prueba, el foco inicial, el foco final, un pattern y una
--   variable sobre la q se hace inducción, se construye la hipótesis inductiva.
createIndHypothesis :: Relation -> PE.Focus -> PE.Focus -> PE.Focus -> Variable 
                       -> Text -> Maybe Hypothesis
createIndHypothesis rel f1 f2 p x nombre = 
    let pattern = PE.toExpr p in
        case pattern of
             (PE.UnOp _ e) -> Just $ createHypothesis nombre (Expr $ hypIndExpr x e)
             -- Si tenemos un constructor binario, vemos si las subexpresiones son del mismo
             -- tipo que toda la expresión. En ese caso tendremos dos hipótesis inductivas, una
             -- por cada subexpresión. Si tenemos una sola expresion del tipo, entonces es similar
             -- al caso operador unario.
             (PE.BinOp op e1 e2) -> 
                let x_type = varTy x in
                    case tType op of
                        t1 :-> t2 :-> t3 ->
                            case (unifyTest t1 x_type,unifyTest t2 x_type) of
                                 (True,True) -> Just $ createHypothesis nombre (Expr $ hypIndExprBin x e1 e2)
                                 (True,False) -> Just $ createHypothesis nombre (Expr $ hypIndExpr x e1)
                                 (False,True) -> Just $ createHypothesis nombre (Expr $ hypIndExpr x e2)
                                 _ -> Nothing
             _ -> Nothing
    -- Expresión que representa la hipótesis inductiva.
    where hypIndExpr x p = PE.BinOp (relToOp rel) (PE.applySubst (PE.toExpr f1) (Map.fromList [(x,p)]))
                                              (PE.applySubst (PE.toExpr f2) (Map.fromList [(x,p)]))
          hypIndExprBin x p1 p2 = PE.BinOp folAnd (hypIndExpr x p1) (hypIndExpr x p2)