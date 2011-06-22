-- | Una Expresión es algo que se puede manipular. Difiere relativamente
-- poco de una PreExpresión.
module Equ.Expr where

import Equ.PreExpr
import Equ.Theories
import Equ.Syntax

-- | Las expresiones son pre-expresiones bien tipadas. Es decir,
-- ningún constituyente de una expresión puede tener TyUnknown como
-- tipo.
newtype Expr = Expr PreExpr