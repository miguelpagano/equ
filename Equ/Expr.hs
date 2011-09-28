-- | Una Expresión es algo que se puede manipular. Difiere
-- relativamente poco de una PreExpresión.
module Equ.Expr where

import Equ.PreExpr.Internal
import Data.Serialize(Serialize, get, put)
-- import Equ.Theories
-- import Equ.Syntax

import Control.Applicative ((<$>))
import Test.QuickCheck(Arbitrary, arbitrary)

-- | Las expresiones son pre-expresiones bien tipadas. Es decir,
-- ningún constituyente de una expresión puede tener TyUnknown como
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

getPreExpr :: Expr -> PreExpr
getPreExpr (Expr e) = e
