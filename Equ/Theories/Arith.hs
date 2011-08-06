-- | La teoría de aritmética.
module Equ.Theories.Arith where

import Prelude hiding (sum)
import Data.Text (pack)

import Equ.Syntax
import Equ.Types
import Equ.Expr
import Equ.PreExpr
-- TODO: Agregar reglas para este módulo.
-- import Equ.Rule 
import Equ.Theories.AbsName

-- Estos módulos definen los símbolos de función
-- que devuelven expresiones de tipo Num.

natZero :: Constant
natZero = Constant { conRepr = pack "0"
                , conName = Zero
                , conTy = TyAtom ATyNat
                }

natSucc :: Operator
natSucc = Operator { opRepr = pack "1+"
                    , opName = Succ
                    , opTy = TyAtom ATyNat :-> TyAtom ATyNat
                    , opAssoc = None
                    , opNotationTy = NPrefix
                    , opPrec = 1 -- Analizar.
                    }
                    
                    
natSum :: Operator
natSum = Operator { opRepr = pack "+"
                  , opName = Sum
                  , opTy = TyAtom ATyNat :-> TyAtom ATyNat :-> TyAtom ATyNat
                  , opAssoc = ALeft
                  , opNotationTy = NInfix
                  , opPrec = 2
                  }
                  
natProd :: Operator
natProd = Operator { opRepr = pack "*"
                   , opName = Prod
                   , opTy = TyAtom ATyNat :-> TyAtom ATyNat :-> TyAtom ATyNat
                   , opAssoc = ALeft
                   , opNotationTy = NInfix
                   , opPrec = 3
                   }
                   
natEq :: Operator
natEq = Operator { opRepr = pack "="
                 , opName = NatEqual -- Aca habia natEqual, 
                                     -- hice una parchada rapida agregando 
                                     -- NatEqual a OpName.
                 , opTy = TyAtom ATyNat :-> TyAtom ATyNat :-> TyAtom ATyBool
                 , opAssoc = ALeft
                 , opNotationTy = NInfix
                 , opPrec = 1
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

-- DEFINIR REGLAS PARA SUM Y PROD. NEUTRO Y OTRAS (ASOCIAT,CONMUT,..)

prod :: Expr -> Expr -> Expr
prod (Expr n) (Expr m) = Expr $ BinOp natProd n m

intToCon :: Int -> PreExpr
intToCon 0 = Con $ natZero { conTy = TyUnknown }
intToCon n = UnOp (natSucc { opTy = TyUnknown }) $ intToCon (n-1)
