-- | Una Expresión es algo que se puede manipular. Difiere relativamente
-- poco de una PreExpresión.
module Equ.Expr where

-- Hacer ciertas manipulaciones sobre Expresiones puede ser costoso y
-- puede convenir tener un tipo SExpr que permita tener versiones
-- eficientes de esas manipulaciones.

import Equ.Theories
import Equ.Annot
import Language.Syntactic.Syntax

-- Pensar en cómo afectan las definiciones de funciones el usuario los
-- módulos de Expr, Parser, PreExpr, TypeChecker.

