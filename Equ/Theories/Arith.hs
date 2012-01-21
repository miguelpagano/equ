-- | La teoría de aritmética.
{-# Language OverloadedStrings #-}
module Equ.Theories.Arith
    ( -- * Constructores y operadores.
      natZero, natSucc, natProd, natSum
    -- ** Listas de constructores y operadores
    , theoryConstantsList
    , theoryOperatorsList
    , theoryQuantifiersList
    -- ** Lista de axiomas de la teoria
    , theoryAxiomList
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
import Equ.PreExpr
-- TODO: Agregar reglas para este módulo.
import Equ.Rule 
import Equ.Proof
import Equ.Theories.AbsName
import Equ.Theories.FOL(equal)

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

one :: Expr
one = successor zero

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

-- Combinadores para axiomas usuales.
-- | Simetria: @e op e' = e' op e@.
symmetry :: (Expr -> Expr -> Expr) -> Expr -> Expr -> Expr
symmetry op e e' = (e `op` e') `equal` (e' `op` e)

-- | Asociatividad: @(e op e') op e'' = e op (e' op e'')@.
associativity :: (Expr -> Expr -> Expr) -> Expr -> Expr -> Expr -> Expr 
associativity op e e' e'' = ((e `op` e') `op` e'') `equal` (e `op` (e' `op` e''))


-- | Neutro a izquierda: @n op e = e@.
leftNeutral :: (Expr -> Expr -> Expr) -> Expr -> Expr -> Expr
leftNeutral op n e = (n `op` e) `equal` e

-- | Neutro a derecha: @n op e = e@.
rightNeutral :: (Expr -> Expr -> Expr) -> Expr -> Expr -> Expr
rightNeutral op n e = (e `op` n) `equal` e

-- | Variables de tipo Nat
varI,varJ,varK :: Expr
varI= Expr $ Var $ var "i" $ TyAtom ATyNat 
varJ= Expr $ Var $ var "j" $ TyAtom ATyNat 
varK= Expr $ Var $ var "k" $ TyAtom ATyNat 

zeroLNeutralSum :: Expr
zeroLNeutralSum = leftNeutral sum zero varI

zeroRNeutralSum :: Expr
zeroRNeutralSum = rightNeutral sum zero varI

symSum :: Expr
symSum = symmetry sum varI varJ

assocSum :: Expr
assocSum = associativity sum varI varJ varK

oneLNeutralProd :: Expr
oneLNeutralProd = leftNeutral prod one varI

oneRNeutralProd :: Expr
oneRNeutralProd = rightNeutral prod one varI

symProd :: Expr
symProd = symmetry prod varI varJ


assocProd :: Expr
assocProd = associativity prod varI varJ varK


-- | Axiomas: los construimos automáticamente.
theoryAxiomList :: [(Text,Expr)]
theoryAxiomList = [ ("Neutro a izquierda de la suma",zeroLNeutralSum)
                  , ("Neutro a derecha de la suma", zeroRNeutralSum)
                  , ("Simetría de la suma", symSum)
                  , ("Asociatividad de la suma", assocSum)
                  -- Producto
                  , ("Neutro a izquierda del producto",oneLNeutralProd)
                  , ("Neutro a derecha del producto", oneRNeutralProd)
                  , ("Simetría del producto", symProd)
                  , ("Asociatividad del producto", assocProd)
                  ]
