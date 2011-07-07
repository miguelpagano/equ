-- | Declaración de los posibles tipos que puede informar el usuario
-- en un árbol de tipado. Si se desea agregar una nueva teoría,
-- entonces es necesario extender los tipos atómicos (o los 
-- constructores de tipos, por ejemplo para árboles binarios).

module Equ.Types where
import Data.Text
import qualified Data.Poset as ModPoset

data AtomTy = ATyNum
            | ATyInt
            | ATyNat
            | ATyBool -- ^ Corresponde a las fórmulas proposicionales.
     deriving (Eq,Show)

data Type = TyUnknown
          | TyVar Text
          | TyList Type
          | TyAtom AtomTy
          | Type :-> Type
    deriving (Eq,Show)


instance ModPoset.Poset Type where
    (<=) (TyAtom ATyNat) (TyAtom ATyInt) = True
    (<=) (TyAtom ATyInt) (TyAtom ATyNum) = True
    (<=) (TyAtom ATyNat) (TyAtom ATyNum) = True
    (<=) (TyList t1) (TyList t2) = t1 ModPoset.<= t2
    (<=) (t1 :-> t2) (s1 :-> s2) = t1 ModPoset.<= t2 && s1 ModPoset.<= s2
    (<=) t1 t2 = t1==t2

