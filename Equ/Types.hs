-- | Declaración de los posibles tipos que puede informar el usuario
-- en un árbol de tipado. Si se desea agregar una nueva teoría,
-- entonces es necesario extender los tipos atómicos (o los 
-- constructores de tipos, por ejemplo para árboles binarios).

module Equ.Types where
import Data.Text
import Data.Poset

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
    
-- | Constructor de TyVar
tyVar :: String -> Type
tyVar = TyVar . pack 

-- | Constructor de TyAtom ATyBool
tyBool :: Type
tyBool = TyAtom ATyBool

instance Poset Type where
    (TyAtom ATyNat) `leq` (TyAtom ATyInt) = True
    (TyAtom ATyInt) `leq` (TyAtom ATyNum) = True
    (TyAtom ATyNat) `leq` (TyAtom ATyNum) = True
    (TyList t1) `leq` (TyList t2) = t1 `leq` t2
    (t1 :-> t2) `leq` (s1 :-> s2) = s1 `leq` t1 && t2 `leq` s2
    t1 `leq` t2 = t1==t2

