module Equ.Rewrite
    (
    exprRewrite
    )
    where

import Equ.Matching
import Equ.Rule
import Equ.Expr
import Equ.PreExpr
import Data.Map

{- | Dada una expresión y una regla, si la expresión matchea con el lado
izquierdo de la regla, entonces se reescribe de acuerdo al lado derecho
de la regla.
-}
exprRewrite :: Expr -> Rule -> Maybe Expr
exprRewrite (Expr e) (Rule{lhs=Expr l,rhs=Expr r}) = match l e >>= 
                                                    Just . Expr . applySubst r
