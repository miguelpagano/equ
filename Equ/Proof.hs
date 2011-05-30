-- | Este módulo define la noción de una prueba.

module Equ.Proof where

import Equ.Expr
import Equ.Theories
import Equ.Rule


{- En principio tendríamos lo siguiente.

data Proof rel ty where    
    Axiom :: Axiom rel ty -> Expr ty -> Expr ty -> Proof ty
    InductionNat :: Expr ty ->  Expr ty -> (Proof Num) -> (Proof Num) -> Proof Num
    Trans :: Expr ty -> Expr ty -> Expr ty -> (Proof rel ty) -> (Proof rel ty) -> Proof rel ty
-}