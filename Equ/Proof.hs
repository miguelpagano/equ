{-# Language GADTs #-}
{-| Este m&#243;dulo define la noci&#243;n de una prueba. -}
module Equ.Proof (
                  -- * Axiomas
                  Axiom(..) 
                 -- * Pruebas
                 , Proof                   
                 ) where


{-  -}
import Equ.Expr
import Equ.PreExpr
import Equ.Theories
import Equ.Rule

import Data.Text
import Data.Map (Map)


-- | Las hip&#243;tesis son nombradas por n&#250;meros.
data Name where
    Index :: Int -> Name

{-|
  Ejemplos de axiomas:

  @ 
  neutralEquiv :: Axiom
  neutralEquiv = Axiom { axName = "Neutro de la equivalencia"
  , axExpr = equiv (equiv True varP) varP
  , axRules = undefined
  }
  @

-}

data Axiom = Axiom {
      axName  :: Text
    , axExpr  :: Expr
    , axRel   :: Relation
    , axRules :: [Rule]
    }
    
-- Un teorema
data Theorem = Theorem {
      thName  :: Text
    , thExpr  :: Expr
    , thRel   :: Relation
    , thProof :: Proof
    , thRules :: [Rule]
    }

-- | El contexto lleva las hip&#243;tesis actuales; en nuestro caso hay
-- tres formas de agregar hip&#243;tesis al contexto: en una prueba por
-- casos hay nuevas igualdades; en una prueba por inducci&#243;n hay
-- hip&#243;tesis inductivas y en una prueba que usa el metateorema de la
-- deducci&#243;n asumimos el antecedente de una implicaci&#243;n.
type Ctx = Map Name Expr

-- | Las pruebas elementales son aplicar un axioma (en un foco), 
-- usar un teorema ya probado, o usar una hip&#243;tesis.
data Basic where
    Ax  :: Axiom -> Basic    -- Un axioma de cierta teor&#237;a.
    Teo :: Theorem -> Basic  -- Un teorema ya probado.
    Hyp :: Name -> Basic   --  Una hip&#243;tesis que aparece en el contexto.               

{- Los tipos de pruebas que contemplamos son:

0. Hueco: representa una prueba incompleta.

1. Paso elemental:
  a.  Axiomas provenientes de las teor&#237;as.
  b.  Teorema.
  c.  Hip&#243;tesis.

2. Transitividad de los operadores de relaci&#243;n sobre los que se
prueban cosas.

3. Combinaci&#243;n de sub-pruebas.

4. Combinaci&#243;n inductiva de sub-pruebas.

Tanto para 3 y 4 es necesario tener informaci&#243;n sobre la 
expresi&#243;n en cuesti&#243;n.

Queremos una relaci&#243;n de orden entre las relaciones para poder
debilitar una prueba de equivalente en una prueba de implicaci&#243;n.

-}

{-| Ejemplos de pruebas:
@
incomplete :: Proof
incomplete = Hole M.empty Equivalence (Top,equiv True True) (Top,True)
@

@
trivial :: Proof
trivial = Simple M.empty Equivalence (Top,equiv True True) (Top,True) $
          Ax neutralEquiv
@

La propiedad importante es que en los pasos simples tenemos alguna
regla asociada al axioma o al teorema usado que hace coincidir (salvo
variables ligadas?) a la primera con la segunda expresi&#243;n:

Si 

@
theo :: Proof
theo = Simple ctx foc foc' $ Ax ax

theo' :: Proof
theo' = Simple ctx foc foc' $ Theo thm
@

entonces @ rewriteInFocus foc ax == foc' @.

Si la prueba es simple y fue usando una hip&#243;tesis, digamos
@
theo2 :: Proof
theo2 = Simple ctx foc foc' $ Hyp n
@ 

entonces ...
-}
data Proof where
    Hole   :: Ctx -> Relation -> Focus -> Focus -> Proof     -- No hay todav&#237;a una prueba.
    Simple :: Ctx -> Relation -> Focus -> Focus -> Basic -> Proof  -- Una prueba con un solo paso.
    Trans  :: Ctx -> Relation -> Focus -> Focus -> Focus -> Proof -> Proof -> Proof -- 
    --  Cases e r e' [(e0,p0),...,(en,pn)] p es una prueba de e r e'
    -- con sub-pruebas p0...pn de e r e' con hip&#243;tesis e_i para cada i
    -- y la exhaustividad de e0 ... en est&#225; dada por p.
    Cases  :: Ctx -> Relation -> Focus -> Focus -> Focus -> [(Focus,Proof)] -> Proof
    -- Demostraci&#243;n por inducci&#243;n en varias expresiones. Es distinta
    -- de la anterior en el sentido que no hay una prueba de
    -- exhaustividad.
    Ind    :: Ctx -> Relation -> Focus -> Focus -> [Focus] -> [([Focus],Proof)] -> Proof
    --  Meta-teorema de la deducci&#243;n.
    Deduc  :: Ctx -> Focus -> Focus -> Proof -> Proof
    --  Enfocarse en una ocurrencia de una subexpresi&#243;n para
    -- "reescribir" la expresi&#243;n original en otra.
    Focus  :: Ctx -> Relation -> Focus -> Focus -> Proof -> Proof
