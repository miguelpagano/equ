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

import Prelude hiding (sum,or,and)
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
import Equ.Proof.Condition

import Control.Applicative
-- Estos módulos definen los símbolos de función
-- que devuelven expresiones de tipo Num.
 
 
-- | Cuantificador Sumatoria
sumQuant :: Quantifier
sumQuant = Quantifier { quantRepr = "∑"
                       , quantName = SumQuant
                       , quantTy = tyVar "A" :-> (TyAtom ATyNat)
                       }


-- | Constantes de arith
theoryConstantsList :: [Constant]
theoryConstantsList = [natZero]
-- | Operadores de  arith
theoryOperatorsList :: [Operator]
theoryOperatorsList = [natSucc,natSum,natProd]
-- | Cuantificadores de arith
theoryQuantifiersList :: [Quantifier]
theoryQuantifiersList = [sumQuant]

-- | Constructor de Variable de tipo Nat.
varNat :: Text -> Expr
varNat s = Expr $ Var $ var s (TyAtom ATyNat)


-- | Constructor de Variable (no de Expr variable) de tipo Nat
metaVarNat :: Text -> Variable
metaVarNat s = var s (TyAtom ATyNat)

-- | Expresiones Meta-Variables de tipo Nat
exprVarNat :: Text -> Expr
exprVarNat s = Expr $ Var $ var s $ TyAtom ATyNat 

-- | Constructor de Constante zero
zero :: Expr
zero = Expr $ Con $ natZero

-- | Constructor de sucesor.
-- PRE: La expresión n es del tipo adecuado
-- Esta aqui porque lo necesitamos para la regla Separacion de termino
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


-- | Expresiones Variables de tipo Nat
varI,varJ,varK :: Expr
varI= Expr $ Var $ var "i" $ TyAtom ATyNat 
varJ= Expr $ Var $ var "j" $ TyAtom ATyNat 
varK= Expr $ Var $ var "k" $ TyAtom ATyNat 
varL= Expr $ Var $ var "l" $ TyAtom ATyNat 
varM= Expr $ Var $ var "m" $ TyAtom ATyNat 

-- | Expresiones Variables Booleanas
varP,varQ :: Expr
varP= Expr $ Var $ var "p" tyBool
varQ= Expr $ Var $ var "q" tyBool

-- | Expresiones Variables de cualquier tipo
varN= Expr $ Var $ var "n" $ tyVar "A"


-- | Variables de cualquier tipo
varX :: Variable
varX = var "x" $ tyVar "A"
varY :: Variable
varY = var "y" $ tyVar "A"




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

evalSum :: Expr
evalSum = equal (sum (successor varI) varJ) (successor (sum varI varJ))

sumQ :: Variable -> Expr -> Expr -> Expr
sumQ v (Expr r) (Expr t) = Expr $ Quant sumQuant v r t


-- | Rango vacío para sumatoria

emptyRangeSum :: (Text,Expr,Condition)
emptyRangeSum = ( "Rango Vacío Sumatoria"
                , emptyRange sumQ equal varX varI zero
                , GenConditions []
                )
                
-- | Rango Unitario para sumatoria
unitRangeSum :: (Text,Expr,Condition)
unitRangeSum = ( "Rango Unitario Sumatoria"
                  , unitRange sumQ equal varX varN varI varJ
                  , GenConditions [ReplacedExpr peVarJ peVarI varX peVarN]
                  )
    where Expr peVarJ = varJ
          Expr peVarI = varI
          Expr peVarN = varN

-- | Partición de Rango para sumatoria.
--  Notar que este axioma tiene una condición de que los operandos de la disyunción
--  del rango sean disjuntos, pero no tenemos manera de expresar eso por el momento.
partRangeSum :: (Text,Expr,Condition)
partRangeSum = ( "Partición de Rango Sumatoria"
               , partRange sumQ equal sum varX varP varQ varI
               , GenConditions []
               )

termRuleSum :: (Text,Expr,Condition)
termRuleSum = ( "Regla del Término Sumatoria"
              , termRule sumQ equal sum varX varP varI varJ
              , GenConditions []
              )
              
distLeftProdSum :: (Text,Expr,Condition)
distLeftProdSum =
    ( "Distributividad a izquierda del * y Sumatoria"
    , distLeftQuant sumQ equal prod varX varP varI varJ
    , GenConditions [VarNotInExpr varX peVarI]
    )
    where Expr peVarI = varI
    
distRightProdSum :: (Text,Expr,Condition)
distRightProdSum =
    ( "Distributividad a derecha del * y Sumatoria"
    , distLeftQuant sumQ equal prod varX varP varI varJ
    , GenConditions [VarNotInExpr varX peVarI]
    )
    where Expr peVarI = varI
          
nestedRuleSum :: (Text,Expr,Condition)
nestedRuleSum =
    ( "Regla de Anidado Sumatoria"
    , nestedRule sumQ equal varX varY varP varQ varI
    , GenConditions [VarNotInExpr varY peVarP]
    )
    where Expr peVarP = varP
    
changeVarSum :: (Text,Expr,Condition)
changeVarSum =
    ( "Regla de Cambio de Variable Sumatoria"
    , changeVar sumQ equal varX varY varP varI varQ varJ
    , GenConditions [ReplacedExpr peVarQ peVarP varX (Var varY),
                     ReplacedExpr peVarJ peVarI varX (Var varY),
                     VarNotInExpr varY peVarP,
                     VarNotInExpr varY peVarI]
    )
    where Expr peVarI = varI
          Expr peVarP = varP
          Expr peVarQ = varQ
          Expr peVarJ = varJ
              
              
--  Axiomas de Menor y Menor o igual. En general en la materia, estos pasos
--  se justifican con "Aritmética". Una cosa que se podría hacer es
--  meter todas las reglas que generan estos axiomas en uno solo que se llame
--  "Aritmética".

-- | Un número es menor que el siguiente
defLessAxiom :: (Text,Expr,Condition)
defLessAxiom =
    ( "Definición de <"
    , equiv (less varI (successor varI)) true
    , GenConditions []
    )
    
-- | Definición de Menor o Igual
defLessOrEq :: (Text,Expr,Condition)
defLessOrEq =
    ( "Definición de ≤"
    , (lessOrEq varI varJ) `equiv` (or (less varI varJ) (equal varI varJ))
    , GenConditions []
    )
    
emptyInterv :: (Text,Expr,Condition)
emptyInterv =
    ( "Intervalo Vacío"
    , (and (lessOrEq varI varJ) (less varJ varI)) `equiv` false
    , GenConditions []
    )
    
arithInterv :: (Text,Expr,Condition)
arithInterv =
    ( "Aritmética en Intervalo"
    , (and (lessOrEq zero varI) (less varI $ successor varK)) `equiv`
      (or (equal varI zero) (and (less zero varI) (less varI $ successor varK)))
    , GenConditions []
    )
    
lessAndLessOrEq :: (Text,Expr,Condition)
lessAndLessOrEq =
    ( "Relación entre < y ≤"
    , (varI `less` varJ) `equiv` ((successor varI) `lessOrEq` varJ)
    , GenConditions []
    )
    
-- | Reindizado
reindAxiom :: (Text,Expr,Condition)
reindAxiom =
    ( "Reindizado Sumatoria"
    , (sumQ (metaVarNat "j") range1 term1) `equal` (sumQ (metaVarNat "j") range2 term2)
    , GenConditions [ReplacedExpr peVarM peVarL (metaVarNat "j") peSuccJ]
    )
    
    where range1 = (and ((successor varI) `lessOrEq` varJ) $ varJ `less` (successor varK))
          term1 = varL
          range2 = (and (varI `lessOrEq` varJ) $ varJ `less` varK)
          term2 = varM
          Expr peVarM = varM
          Expr peVarL = varL
          Expr peSuccJ = successor varJ
              
       
-- | Axiomas: los construimos automáticamente.
theoryAxiomList :: [(Text,Expr,Condition)]
theoryAxiomList = [ ("Evaluar suma", evalSum,GenConditions [])
                  , ("Neutro a izquierda de la suma",zeroLNeutralSum,GenConditions [])
                  , ("Neutro a derecha de la suma", zeroRNeutralSum,GenConditions [])
                  , ("Simetría de la suma", symSum,GenConditions [])
                  , ("Asociatividad de la suma", assocSum,GenConditions [])
                  -- Producto
                  , ("Neutro a izquierda del producto",oneLNeutralProd,GenConditions [])
                  , ("Neutro a derecha del producto", oneRNeutralProd,GenConditions [])
                  , ("Simetría del producto", symProd,GenConditions [])
                  , ("Asociatividad del producto", assocProd,GenConditions [])
                  , emptyRangeSum, unitRangeSum, partRangeSum, termRuleSum
                  , distLeftProdSum, distRightProdSum, nestedRuleSum, changeVarSum
                  , emptyInterv, arithInterv, lessAndLessOrEq, reindAxiom
                  , defLessAxiom, defLessOrEq
                  ]

