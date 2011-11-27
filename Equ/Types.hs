{-| Este modulo contiene la declaracion de los posibles tipos para
los términos de las (pre-)expresiones. Como en las pre-expresiones,
declaramos un tipo de datos general que nos permite utilizar muchas
funciones e idiomas estándares de Haskell.  -}

{-# Language TypeSynonymInstances #-}
module Equ.Types where

import Data.Text (Text, pack, unpack)
import Data.Poset

import Control.Applicative
import Test.QuickCheck(Arbitrary, arbitrary, elements, oneof)
import Data.Monoid
import qualified Data.Foldable as F
import Data.Traversable
import Data.Serialize(Serialize, get, getWord8, put, putWord8)

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


instance Functor Type' where
    fmap f (TyVar v) = TyVar $ f v
    fmap f (TyList t) = TyList $ fmap f t
    fmap f (t :-> t') = fmap f t :-> fmap f t'
    fmap _ (TyAtom a) = TyAtom a
    fmap _ TyUnknown = TyUnknown

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

instance Serialize TyVarName where
    put = put . unpack
    get = get >>= return . pack

instance Serialize AtomTy where
    put ATyNum = putWord8 0
    put ATyInt = putWord8 1
    put ATyNat = putWord8 2
    put ATyBool = putWord8 3
    
    get = do
    tag_ <- getWord8
    case tag_ of
        0 -> return ATyNum
        1 -> return ATyInt
        2 -> return ATyNat
        3 -> return ATyBool
        _ -> fail $ "SerializeErr AtomTy " ++ show tag_

instance (Serialize a) => Serialize (Type' a) where
    put TyUnknown = putWord8 0
    put (TyVar v) = putWord8 1 >> put v
    put (TyList t) = putWord8 2 >> put t
    put (TyAtom a) = putWord8 3 >> put a
    put (t :-> t') = putWord8 4 >> put t >> put t'

    get = do
    tag_ <- getWord8
    case tag_ of
        0 -> return TyUnknown
        1 -> TyVar <$> get
        2 -> TyList <$> get
        3 -> TyAtom <$> get
        4 -> (:->) <$> get <*> get
        _ -> fail $ "SerializeErr (Type' a) " ++ show tag_

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
