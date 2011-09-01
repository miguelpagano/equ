-- | Definición de los errores de matching.

module Equ.Matching.Error where
import Equ.PreExpr

-- | Errores de matching.
data MatchError = DoubleMatch Variable PreExpr PreExpr
                | BindingVar Variable
                | InequPreExpr PreExpr PreExpr
                | InequOperator Operator Operator
                | InequQuantifier Quantifier Quantifier
                deriving (Show, Eq)