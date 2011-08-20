-- | Este módulo define la noción de una prueba.
{-# Language GADTs #-}

module Equ.Proof where

import Equ.Expr
import Equ.PreExpr
import Equ.Theories
import Equ.Rule

{- Los tipos de pruebas que contemplamos son:

0. Hueco.
1. Paso elemental:
  a.  Axiomas provenientes de las teorías.
  b.  Teorema.
  c.  Hipótesis.
2. Transitividad de los operadores de relación sobre los que
   se prueban cosas.
3. Combinación de sub-pruebas.
4. Combinación inductiva de sub-pruebas.

Tanto para 3 y 4 es necesario tener información sobre la 
expresión en cuestión.

Queremos una relación de orden entre las relaciones para poder
debilitar una prueba de equivalente en una prueba de implicación.

-}

data Name where
    Name :: Int -> Name

data Axiom = Axiom 
data Theorem = Theorem
data Hypothesis = Hypo

type Ctx = Map Name Hypothesis

data Basic where
    Ax  :: Axiom -> Basic    -- ^ Un axioma de cierta teoría.
    Teo :: Theorem -> Basic  -- ^ Un teorema ya probado.
    Hyp :: Name -> Ctx -> Basic   -- ^ Una hipótesis que aparece en el contexto.               

data Proof where
    Hole   :: Ctx -> Relation -> Focus -> Focus -> Proof     -- ^ No hay todavía una prueba.
    Simple :: Ctx -> Relation -> Focus -> Focus -> Basic -> Proof  -- ^ Una prueba con un solo paso.
    Trans  :: Ctx -> Relation -> Focus -> Focus -> Focus -> Proof -> Proof -> Proof -- ^
    -- | Cases e r e' [(e0,p0),...,(en,pn)] p es una prueba de e r e'
    -- con sub-pruebas p0...pn de e r e' con hipótesis e_i para cada i
    -- y la exhaustividad de e0 ... en está dada por p.
    Cases  :: Ctx -> Relation -> Focus -> Focus -> Focus -> [(Focus,Proof)] -> Proof
    -- | Demostración por inducción en varias expresiones. Es distinta
    -- de la anterior en el sentido que no hay una prueba de
    -- exhaustividad.
    Ind    :: Ctx -> Relation -> Focus -> Focus -> [Focus] -> [([Focus],Proof)] -> Proof
    -- | Meta-teorema de la deducción.
    Deduc  :: Ctx -> Focus -> Focus -> Proof -> Proof
    -- | Enfocarse en una ocurrencia de una subexpresión para
    -- "reescribir" la expresión original en otra.
    Focus  :: Ctx -> Relation -> Focus -> Focus -> Proof -> Proof

{- 

Prueba por casos:

{- En principio tendríamos lo siguiente.

data Proof rel ty where    
    Axiom :: Axiom rel ty -> Expr ty -> Expr ty -> Proof ty
    InductionNat :: Expr ty ->  Expr ty -> (Proof Num) -> (Proof Num) -> Proof Num
    Trans :: Expr ty -> Expr ty -> Expr ty -> (Proof rel ty) -> (Proof rel ty) -> Proof rel ty
-}