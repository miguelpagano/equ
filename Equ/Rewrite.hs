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

import Control.Applicative ((<$>))

{-| Dada una expresión y una regla, si la expresión matchea con el lado
izquierdo de la regla, entonces se reescribe de acuerdo al lado derecho
de la regla.
-}
exprRewrite :: Expr -> Rule -> Maybe Expr
exprRewrite (Expr e) rule = Expr . applySubst r <$> match l e
    where (Expr r) = rhs rule
          (Expr l) = lhs rule

