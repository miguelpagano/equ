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
import Equ.TypeChecker(unifyTest,match)
import Equ.Theories(relToOp, createHypothesis)
import Equ.Rule(Relation)

import qualified Data.Map as Map
import Data.Text

-- | Dada la relacion de una prueba, el foco inicial, el foco final, un pattern y una
--   variable sobre la q se hace inducción, se construye la hipótesis inductiva.

-- Asume que el pattern es un constructor inductivo.
createIndHypothesis :: Relation -> PE.Focus -> PE.Focus -> PE.Focus -> Variable 
                       -> Text -> Maybe Hypothesis
createIndHypothesis rel f1 f2 p x nombre = 
    let pattern = PE.toExpr p in
        case pattern of
             (PE.UnOp _ e) -> Just $ createHypothesis nombre (Expr $ hypIndExpr x e) [InductiveHypothesis e]
             -- Si tenemos un constructor binario, tenemos que ver si los parámetros
             -- del operador son del tipo inductivo. Si ambos lo son, la HI quedará
             -- como un "y" lógico de las dos subhipótesis inductivas (vale para el operando izquierdo
             -- y vale para el operando derecho). Si 
             (PE.BinOp op e1 e2) -> 
                let x_type = varTy x in
                    case tType op of
                        t1 :-> t2 :-> t3 ->
                            --case (unifyTest t1 x_type,unifyTest t2 x_type) of
                            case (matchType t1 x_type,matchType t2 x_type) of  
                                 -- VER ESTE CASO: DEberian crearse DOS HI en vez de una con una conjunción.
                                 (True,True) -> Just $ createHypothesis nombre (Expr $ hypIndExprBin x e1 e2) []
                                 (True,False) -> Just $ createHypothesis nombre (Expr $ hypIndExpr x e1) [InductiveHypothesis e1]
                                 (False,True) -> Just $ createHypothesis nombre (Expr $ hypIndExpr x e2) [InductiveHypothesis e2]
                                 _ -> Nothing
             _ -> Nothing
    -- Expresión que representa la hipótesis inductiva.
    where hypIndExpr x p = PE.BinOp (relToOp rel) 
                                    (PE.applySubst (PE.toExpr f1) subst)
                                    (PE.applySubst (PE.toExpr f2) subst)
              where subst = Map.singleton x p
          hypIndExprBin x p1 p2 = PE.BinOp folAnd (hypIndExpr x p1) (hypIndExpr x p2)
          
          matchType t t' = match t t' && match t' t