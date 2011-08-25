-- | La teoría de aritmética.
{-# Language OverloadedStrings #-}
module Equ.Theories.Arith
    ( -- * Constructores y operadores.
      natZero, natSucc, natProd, natSum
    -- ** Listas de constructores y operadores
    , theoryConstantsList
    , theoryOperatorsList
    , theoryQuantifiersList
    -- * Versión tipada de operadores.
    , varNat, zero, successor, prod
    , intToCon
    )
    where

import Prelude hiding (sum)
import Data.Text (Text)

import Equ.Syntax
import Equ.Types
import Equ.Expr
import Equ.PreExpr.Internal
-- TODO: Agregar reglas para este módulo.
-- import Equ.Rule 
import Equ.Theories.AbsName

-- Estos módulos definen los símbolos de función
-- que devuelven expresiones de tipo Num.
 
-- | Constante cero.
natZero :: Constant
natZero = Constant { conRepr = "0"
                   , conName = Zero
                   , conTy = TyAtom ATyNat
                   }

-- | Operador sucesor.
natSucc :: Operator
natSucc = Operator { opRepr = "succ"
                   , opName = Succ
                   , opTy = TyAtom ATyNat :-> TyAtom ATyNat
                   , opAssoc = None
                   , opNotationTy = NPrefix
                   , opPrec = 23 -- Analizar.
                   }

-- | Operador suma.
natSum :: Operator
natSum = Operator { opRepr = "+"
                  , opName = Sum
                  , opTy = TyAtom ATyNat :-> TyAtom ATyNat :-> TyAtom ATyNat
                  , opAssoc = ALeft
                  , opNotationTy = NInfix
                  , opPrec = 21
                  }

-- | Operador producto.
natProd :: Operator
natProd = Operator { opRepr = "*"
                   , opName = Prod
                   , opTy = TyAtom ATyNat :-> TyAtom ATyNat :-> TyAtom ATyNat
                   , opAssoc = ALeft
                   , opNotationTy = NInfix
                   , opPrec = 22
                   }

-- | Constantes de arith
theoryConstantsList :: [Constant]
theoryConstantsList = [natZero]
-- | Operadores de  arith
theoryOperatorsList :: [Operator]
theoryOperatorsList = [natSucc,natSum,natProd]
-- | Cuantificadores de arith
theoryQuantifiersList :: [Quantifier]
theoryQuantifiersList = []

-- | Constructor de Variable de tipo Nat.
varNat :: Text -> Expr
varNat s = Expr $ Var $ var s (TyAtom ATyNat)

-- | Constructor de Constante zero
zero :: Expr
zero = Expr $ Con $ natZero

-- | Constructor de sucesor.
-- PRE: La expresión n es del tipo adecuado
successor :: Expr -> Expr
successor (Expr n) = Expr $ UnOp natSucc n

-- | Constructor de suma
-- PRE: Las expresiones deben ser del tipo correcto
sum :: Expr -> Expr-> Expr
sum (Expr n) (Expr m) = Expr $ BinOp natSum n m

-- DEFINIR REGLAS PARA SUM Y PROD. NEUTRO Y OTRAS (ASOCIAT,CONMUT,..)

prod :: Expr -> Expr -> Expr
prod (Expr n) (Expr m) = Expr $ BinOp natProd n m

intToCon :: Int -> PreExpr
intToCon 0 = Con $ natZero { conTy = TyUnknown }
intToCon n = UnOp (natSucc { opTy = TyUnknown }) $ intToCon (n-1)
