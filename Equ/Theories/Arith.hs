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
import Equ.PreExpr.Symbols
import Equ.PreExpr.Eval
-- TODO: Agregar reglas para este módulo.
import Equ.Rule 
import Equ.Theories.AbsName
import Equ.Theories.Common

import Control.Applicative
-- Estos módulos definen los símbolos de función
-- que devuelven expresiones de tipo Num.
 

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
symSum = symmetryEqual sum varI varJ

assocSum :: Expr
assocSum = associativityEqual sum varI varJ varK

oneLNeutralProd :: Expr
oneLNeutralProd = leftNeutral prod one varI

oneRNeutralProd :: Expr
oneRNeutralProd = rightNeutral prod one varI

symProd :: Expr
symProd = symmetryEqual prod varI varJ

assocProd :: Expr
assocProd = associativityEqual prod varI varJ varK


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

