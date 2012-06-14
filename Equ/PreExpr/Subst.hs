-- | En este modulo definimos las funciones necesarias para analizar el
--  matching entre preExpresiones.
module Equ.PreExpr.Subst
    ( applySubst
    , ExprSubst
    )
    where

import Equ.Syntax
import Equ.PreExpr.Internal

import qualified Data.Map as M
import Control.Arrow((***))
-- | Mapa de substituciones de variable - preExpresiones.
type ExprSubst = M.Map Variable PreExpr

-- | Aplica una substituci&#243;n a una expresi&#243;n dada.
applySubst :: PreExpr -> ExprSubst -> PreExpr
applySubst (Var v) s = M.findWithDefault (Var v) v s
applySubst (UnOp op e) s = UnOp op $ applySubst e s
applySubst (BinOp op e f) s = BinOp op (applySubst e s) (applySubst f s)
applySubst (App e f) s = App (applySubst e s) (applySubst f s)
applySubst (Quant q v e1 e2) s = Quant q v (applySubst e1 s) (applySubst e2 s)
applySubst (Paren e) s = Paren $ applySubst e s
applySubst (PrExHole h) _ = PrExHole h
applySubst (Con c) _ = Con c
applySubst (Fun f) _ = Fun f
applySubst (If b t f) s = If (applySubst b s) (applySubst t s) (applySubst f s)
applySubst (Case e cs) s = Case (applySubst e s) (map (flip applySubst s *** flip applySubst s) cs)

