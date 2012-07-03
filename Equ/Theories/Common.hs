{-# Language OverloadedStrings #-}
module Equ.Theories.Common where

import Equ.Syntax
import Equ.Types
import Equ.Expr
import Equ.PreExpr
import Equ.Rule
import Equ.Theories.AbsName


-- | Constante True
folTrue :: Constant
folTrue = Constant { conRepr = "True"
                   , conName = CTrue
                   , conTy = tyBool
                   }

-- | Constante False  
folFalse :: Constant          
folFalse = Constant { conRepr = "False"
                    , conName = CFalse
                    , conTy = tyBool
                    }
                     


-- | Equivalencia &#8801;
folEquiv :: Operator
folEquiv = Operator { opRepr = "≡"
                    , opName = Equival
                    , opTy = tyBool :-> tyBool :-> tyBool
                    , opAssoc = ALeft
                    , opNotationTy = NInfix
                    , opPrec = 1
                    , opGlyphs = ["=="]
                    }

-- | Igualdad =
folEqual :: Operator
folEqual = Operator { opRepr = "="
                    , opName = Equal
                    , opTy = tyVar "A" :-> tyVar "A" :-> tyBool
                    , opAssoc = ALeft
                    , opNotationTy = NInfix
                    , opPrec = 5
                    , opGlyphs = []
                    }

-- | Igualdad
equal :: Expr -> Expr -> Expr
equal (Expr a) (Expr b) = Expr $ BinOp folEqual a b

-- | Constructor de Constantes logicas
true :: Expr
true = Expr $ Con $ folTrue

false :: Expr
false = Expr $ Con $ folFalse


-- | Equivalencia
equiv :: Expr -> Expr -> Expr
equiv (Expr p) (Expr q) = Expr $ BinOp folEquiv p q


-- Combinadores para axiomas usuales.
symmetryEquiv :: (Expr -> Expr -> Expr) -> Expr -> Expr -> Expr
symmetryEquiv op e e' = (e `op` e') `equiv` (e' `op` e)

-- | Asociatividad: @(e op e') op e'' = e op (e' op e'')@.
associativityEquiv :: (Expr -> Expr -> Expr) -> Expr -> Expr -> Expr -> Expr 
associativityEquiv op e e' e'' = ((e `op` e') `op` e'') `equiv` (e `op` (e' `op` e''))

-- | Neutro a izquierda: @n op e = e@.
leftNeutralEquiv :: (Expr -> Expr -> Expr) -> Expr -> Expr -> Expr
leftNeutralEquiv op n e = (n `op` e) `equiv` e

-- | Neutro a derecha: @n op e = e@.
rightNeutralEquiv :: (Expr -> Expr -> Expr) -> Expr -> Expr -> Expr
rightNeutralEquiv op n e = (e `op` n) `equiv` e


-- | Simetria: @e op e' = e' op e@.
symmetryEqual :: (Expr -> Expr -> Expr) -> Expr -> Expr -> Expr
symmetryEqual op e e' = (e `op` e') `equal` (e' `op` e)

-- | Asociatividad: @(e op e') op e'' = e op (e' op e'')@.
associativityEqual :: (Expr -> Expr -> Expr) -> Expr -> Expr -> Expr -> Expr 
associativityEqual op e e' e'' = ((e `op` e') `op` e'') `equal` (e `op` (e' `op` e''))



-- | Neutro a izquierda: @n op e = e@.
leftNeutral :: (Expr -> Expr -> Expr) -> Expr -> Expr -> Expr
leftNeutral op n e = (n `op` e) `equal` e

-- | Neutro a derecha: @n op e = e@.
rightNeutral :: (Expr -> Expr -> Expr) -> Expr -> Expr -> Expr
rightNeutral op n e = (e `op` n) `equal` e


-- | 
isTrue :: PreExpr -> Bool
isTrue (Con t) = conName t == CTrue
isTrue _ = False


-- | 
isFalse :: PreExpr -> Bool
isFalse (Con t) = conName t == CFalse
isFalse _ = False