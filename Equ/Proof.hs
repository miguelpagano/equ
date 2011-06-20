-- | Este módulo define la noción de una prueba.
{-# Language GADTs #-}

module Equ.Proof where

import Equ.Expr
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
    
data Basic ctx where
    Ax  :: Axiom -> Basic ctx    -- ^ Un axioma de cierta teoría.
    Teo :: Theorem -> Basic ctx  -- ^ Un teorema ya probado.
    Hyp :: Name -> Basic ctx  -- ^ Una hipótesis que aparece en el contexto.               

data Proof ctx expr rel  where
    Hole   :: expr -> rel -> expr -> Proof ctx expr rel     -- ^ No hay todavía una prueba.
    Simple :: expr -> rel -> expr -> Basic ctx -> Proof ctx expr rel  -- ^ Una prueba con un solo paso.
    Trans  :: expr -> rel -> expr -> Proof ctx expr rel -> Proof ctx expr rel -> Proof ctx expr rel -- ^
    -- | Cases e r e' [(e0,p0),...,(en,pn)] p es una prueba de e r e'
    -- con sub-pruebas p0...pn de e r e' con hipótesis e_i para cada i
    -- y la exhaustividad de e0 ... en está dada por p.
    Cases  :: expr -> rel -> expr -> [(expr,Proof ctx expr rel)] -> Proof ctx expr rel -> Proof ctx expr rel 
    -- | Demostración por inducción en varias expresiones. Es distinta de la anterior en el 
    -- sentido que no hay una prueba de exhaustividad.
    Ind    :: expr -> rel -> expr -> [expr] -> [([expr],Proof ctx expr rel)] -> Proof ctx expr rel 
    -- | Meta-teorema de la deducción.
    Deduc  :: expr -> expr -> Proof ctx expr rel -> Proof ctx expr rel
    -- | Enfocarse en una ocurrencia de una subexpresión para "reescribir" la expresión
    -- original en otra.
    Focus  :: expr -> rel -> expr -> Occur expr -> Proof ctx expr rel -> Proof ctx expr rel

{- En principio tendríamos lo siguiente.

data Proof rel ty where    
    Axiom :: Axiom rel ty -> Expr ty -> Expr ty -> Proof ty
    InductionNat :: Expr ty ->  Expr ty -> (Proof Num) -> (Proof Num) -> Proof Num
    Trans :: Expr ty -> Expr ty -> Expr ty -> (Proof rel ty) -> (Proof rel ty) -> Proof rel ty
-}