-- | La teoría de aritmética.
module Equ.Theories.Arith where

import Prelude hiding (sum)
import Data.Text (pack)

import Equ.Syntax
import Equ.Types
import Equ.Expr
import Equ.PreExpr
import Equ.Rule
import Equ.Theories.AbsName

-- Estos módulos definen los símbolos de función
-- que devuelven expresiones de tipo Num.

natZero :: Constant
natZero = Constant { conRepr = pack "0"
                , conName = Zero
                , conTy = TyAtom ATyNat
                }

natSucc :: Operator
natSucc = Operator { opRepr = pack "+1"
                    , opName = Succ
                    , opTy = TyAtom ATyNat :-> TyAtom ATyNat
                    }
                    
                    
natSum :: Operator
natSum = Operator { opRepr = pack "+"
                  , opName = Sum
                  , opTy = TyAtom ATyNat :-> TyAtom ATyNat :-> TyAtom ATyNat
                  }


-- Constructor de Variable de tipo Nat.
varNat :: String -> Expr
varNat s = Expr $ Var $ var s (TyAtom ATyNat)

-- Constructor de Constante zero
zero :: Expr
zero = Expr $ Con $ natZero

-- Constructor de sucesor.
-- PRE: La expresión n es del tipo adecuado
successor :: Expr -> Expr
successor (Expr n) = Expr $ UnOp natSucc n

-- Constructor de suma
-- PRE: Las expresiones deben ser del tipo correcto
sum :: Expr -> Expr-> Expr
sum (Expr n) (Expr m) = Expr $ BinOp natSum n m