-- | Declaración de los posibles tipos que puede informar el usuario
-- en un árbol de tipado. Si se desea agregar una nueva teoría,
-- entonces es necesario extender los tipos atómicos (o los 
-- constructores de tipos, por ejemplo para árboles binarios).

module Equ.Types where

import Data.Text (Text, pack)
import Data.Poset
import Control.Applicative((<$>),(<*>))
import Test.QuickCheck(Arbitrary, arbitrary, elements, oneof)

data AtomTy = ATyNum
            | ATyInt
            | ATyNat
            | ATyBool -- ^ Corresponde a las fórmulas proposicionales.
     deriving (Eq,Show)

type TyVarName = Text

data Type = TyUnknown
          | TyVar TyVarName
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

<<<<<<< HEAD

-- | Occurence of a type-variable in a type.
occurs :: TyVarName -> Type -> Bool
occurs v (TyVar w) = v == w
occurs v (TyList t) = occurs v t
occurs v (t :-> t') = occurs v t || occurs v t'
occurs _ _ = False

-- | Replace the occurrence of a type-variable for a type: 'replace v
-- s t', replaces the occurences of 'v' in 's' for 't'.
tyreplace :: TyVarName -> Type -> Type -> Type
tyreplace v (TyVar w) t | v == w = t
                        | otherwise = TyVar w
tyreplace v (TyAtom s) _ = TyAtom s
tyreplace v (TyList s) t = TyList $ tyreplace v s t
tyreplace v (s :-> s') t = tyreplace v s t :-> tyreplace v s' t
=======
-- | Instancia arbitrary para text, en principio no la usamos; 
-- generaba demasiada aleatoriedad de preExpr y no servia de mucho.
-- Generaba por ejemplo cosas como (+)(Forall) in (and) | ((ForSome) + (A))
instance Arbitrary Text where
    arbitrary = 
        oneof [ return (pack "ForAll")
                , return (pack "ForSome")
                , return (pack "+")
                , return (pack "-")
                , return (pack "*")
                , return (pack "/")
                , return (pack "and")
                , return (pack "or")
                , return (pack "implies")
                , return (pack "iff")
                ]

-- | Instancia arbitrary para los tipos atómicos.
instance Arbitrary AtomTy where
    arbitrary = elements [ATyNum, ATyInt, ATyNat, ATyBool]
    
-- | Instancia arbitrary para los tipos generales.
instance Arbitrary Type where
    arbitrary = 
        oneof [ return TyUnknown
                , TyVar <$> arbitrary
                , TyList <$> arbitrary
                , TyAtom <$> arbitrary
                , (:->) <$> arbitrary <*> arbitrary
                ]
>>>>>>> 35ba8c7fc98de935caf41e72e562094f493f6d40
