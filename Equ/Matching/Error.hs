-- | Definición de los errores de matching.

module Equ.Matching.Error where
import Equ.PreExpr

-- | Errores de matching.
data MatchError = DoubleMatch Variable FlatExpr FlatExpr
                | BindingVar Variable
                | InequPreExpr FlatExpr FlatExpr
                | InequOperator Operator Operator
                | InequQuantifier Quantifier Quantifier
                | SubTermsAC Operator [FlatExpr] [FlatExpr]
                | NOperands Operator [FlatExpr] [FlatExpr]
                deriving Eq

-- | Pretty print de errores de matching.
instance Show MatchError where
    show (DoubleMatch v pe pe') = "Variable \"" ++ show v ++ 
                                "\" matched with \"" ++ show pe ++ 
                                "\" fail to match with \"" ++ show pe' ++ "\""
    show (BindingVar v) = "Binding variable \"" ++ show v ++ "\""
    show (InequPreExpr e e')  = "\"" ++ show e ++ 
                                    "\" =/= \"" ++ 
                                    show e' ++ "\""
    show (InequOperator e e')  = "\"" ++ show e ++ 
                                    "\" =/= \"" ++ 
                                    show e' ++ "\""
    show (InequQuantifier e e')  = "\"" ++ show e ++ 
                                    "\" =/= \"" ++ 
                                    show e' ++ "\""                                 
    show _ = "otro error"
