-- | Declaración de los posibles tipos que puede informar el usuario
-- en un árbol de tipado. Si se desea agregar una nueva teoría,
-- entonces es necesario extender los tipos atómicos (o los 
-- constructores de tipos, por ejemplo para árboles binarios).

module Equ.Types where
import Data.Text

data AtomTy = ATyNum
            | ATyInt
            | ATyNat
            | ATyBool -- ^ Corresponde a las fórmulas proposicionales.

data Type = TyUnknown
          | TyVar Text
          | TyList Type
          | TyAtom AtomTy
          | Type :-> Type
