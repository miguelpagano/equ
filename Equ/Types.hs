-- | Declaración de los posibles tipos que puede informar el usuario
-- en un árbol de tipado. Si se desea agregar una nueva teoría,
-- entonces es necesario extender los tipos atómicos (o los 
-- constructores de tipos, por ejemplo para árboles binarios).
{-# Language TypeSynonymInstances #-}
module Equ.Types where

import Data.Text (Text, pack)
import Data.Poset

import Control.Applicative
import Test.QuickCheck(Arbitrary, arbitrary, elements, oneof)
import Data.Monoid
import qualified Data.Foldable as F
import Data.Traversable

-- | Tipos de datos atómicos.
data AtomTy = ATyNum  -- ^ Los reales.
            | ATyInt  -- ^ Los enteros.
            | ATyNat  -- ^ Los naturales.
            | ATyBool -- ^ Corresponde a las fórmulas proposicionales.
     deriving (Eq,Show)

-- | Las variables de tipo.
type TyVarName = Text

infixr 8 :->

-- | Un tipo polimórfico para tener instancias de Functor y Monad; las
-- variables de tipo se asumen cuantificadas universalmente.
data Type' v = TyUnknown            -- ^ Representa falta de información.
             | TyVar v              -- ^ Variable de tipo.
             | TyList (Type' v)     -- ^ Listas.
             | TyAtom AtomTy        -- ^ Tipos atómicos.
             | Type' v :-> Type' v  -- ^ Espacios de funciones.
    deriving (Eq,Show)

instance Applicative Type' where
    pure = TyVar
    _ <*> TyUnknown = TyUnknown
    _ <*> TyAtom a = TyAtom a
    TyVar f <*> TyVar v = TyVar $ f v
    TyAtom a <*> TyVar _ = TyAtom a
    TyUnknown <*> TyVar _ = TyUnknown
    TyList f <*> TyVar v = TyList $ f <*> TyVar v
    (f :-> f') <*> TyVar v = (f <*> TyVar v) :-> (f' <*> TyVar v)
    f <*> TyList t = TyList $ (f <*> t)
    f <*> t :-> t' = (f <*> t) :-> (f <*> t')

instance Functor Type' where
    fmap f (TyVar v) = TyVar $ f v
    fmap f (TyList t) = TyList $ fmap f t
    fmap f (t :-> t') = fmap f t :-> fmap f t'
    fmap _ (TyAtom a) = TyAtom a
    fmap _ TyUnknown = TyUnknown

instance F.Foldable Type' where
    foldMap f (TyVar e) = f e
    foldMap f (TyList t) = F.foldMap f t
    foldMap f (t :-> t') = F.foldMap f t `mappend` F.foldMap f t'
    foldMap _ _ = mempty


-- TODO: tiene sentido?
instance Traversable Type' where
    traverse f (TyVar e) = TyVar <$> f e
    traverse f (TyList t) = TyList <$> traverse f t
    traverse f (t :-> t') = liftA2 (:->) (traverse f t) (traverse f t')
    traverse _ TyUnknown = pure TyUnknown
    traverse _ (TyAtom a) = pure (TyAtom a)

instance Monad Type' where
    return a = TyVar a
    TyUnknown >>= _ = TyUnknown
    TyAtom t >>= _ = TyAtom t
    TyVar v >>= f = f v
    TyList t >>= f = TyList $ t >>= f
    t :-> t' >>= f = (:->) (t >>= f) (t' >>= f)

-- | El tipo concreto de nuestras expresiones.
type Type = Type' TyVarName
    
instance Poset Type where
    (TyAtom ATyNat) `leq` (TyAtom ATyInt) = True
    (TyAtom ATyInt) `leq` (TyAtom ATyNum) = True
    (TyAtom ATyNat) `leq` (TyAtom ATyNum) = True
    (TyList t1) `leq` (TyList t2) = t1 `leq` t2
    (t1 :-> t2) `leq` (s1 :-> s2) = s1 `leq` t1 && t2 `leq` s2
    t1 `leq` t2 = t1==t2

-- | Constructor de TyVar
tyVar :: String -> Type
tyVar = TyVar . pack 

-- | Constructor de TyAtom ATyBool
tyBool :: Type
tyBool = TyAtom ATyBool

-- | Ocurencia de una variable en un tipo.
occurs :: TyVarName -> Type -> Bool
occurs v = F.elem v

-- | Replace the occurrence of a type-variable for a type: 'replace v
-- s t', replaces the occurences of 'v' in 's' for 't'.
tyreplace :: TyVarName -> Type -> Type -> Type
tyreplace v t t' = t' >>= (\w -> if v == w then t else TyVar w) 


-- | Instancia arbitrary para el tipo nombre de variable. 
instance Arbitrary TyVarName where
    arbitrary = 
        elements [(pack . ("t"++) . show) n | n <- [(0::Int)..100]]

-- | Instancia arbitrary para los tipos atómicos.
instance Arbitrary AtomTy where
    arbitrary = elements [ATyNum, ATyInt, ATyNat, ATyBool]
    
-- | Instancia arbitrary para los tipos generales.
instance Arbitrary Type where
    arbitrary = 
        oneof [ TyVar <$> arbitrary
              , TyList <$> arbitrary
              , TyAtom <$> arbitrary
              , (:->) <$> arbitrary <*> arbitrary
              ]
