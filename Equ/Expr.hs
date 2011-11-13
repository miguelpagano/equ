-- | Una Expresi&#243;n es algo que se puede manipular. Difiere
-- relativamente poco de una PreExpresi&#243;n.
module Equ.Expr where

import Equ.PreExpr(PreExpr)
import Data.Serialize(Serialize, get, put)

import Control.Applicative ((<$>))
import Test.QuickCheck(Arbitrary, arbitrary)

-- | Las expresiones son pre-expresiones bien tipadas. Es decir,
-- ning&#250;n constituyente de una expresi&#243;n puede tener TyUnknown como
-- tipo.
newtype Expr = Expr PreExpr

instance Show Expr where 
    show (Expr e) = show e

instance Eq Expr where
    (Expr e1) == (Expr e2) = e1 == e2

instance Arbitrary Expr where
    arbitrary = Expr <$> arbitrary

instance Serialize Expr where
    put (Expr e) = put e
    get = Expr <$> get

-- | Retorna la preExpresi&#243;n que constituye la expresi&#243;n.
getPreExpr :: Expr -> PreExpr
getPreExpr (Expr e) = e
