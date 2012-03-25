{-# LANGUAGE TypeSynonymInstances,FlexibleInstances #-}
module Equ.PreExpr.Internal where

import Equ.Syntax
import Control.Applicative ((<$>), (<*>),Applicative(..))
import Test.QuickCheck(Arbitrary, arbitrary, oneof)

import Data.Serialize(Serialize, get, getWord8, put, putWord8)

data PreExpr' a = Var a
                | Con Constant
                | Fun Func
                | PrExHole Hole
                | UnOp Operator (PreExpr' a)
                | BinOp Operator (PreExpr' a) (PreExpr' a)
                | App (PreExpr' a) (PreExpr' a)
                | Quant Quantifier a (PreExpr' a) (PreExpr' a)
                | Paren (PreExpr' a)
                  deriving Eq

--  Instancia binary para PreExpr' a.
instance Serialize a => Serialize (PreExpr' a) where
    put (Var a) = putWord8 0 >> put a
    put (Con c) = putWord8 1 >> put c
    put (Fun f) = putWord8 2 >> put f
    put (PrExHole h) = putWord8 3 >> put h
    put (UnOp op pe) = putWord8 4 >> put op >> put pe
    put (BinOp op pe pe') = putWord8 5 >> put op >> put pe >> put pe'
    put (App pe pe') = putWord8 6 >> put pe >> put pe'
    put (Quant q a pe pe') = putWord8 7 >> put q >> put a >> put pe >> put pe'
    put (Paren pe) = putWord8 8 >> put pe

    get = do
    tag_ <- getWord8
    case tag_ of
        0 -> Var <$> get
        1 -> Con <$> get
        2 -> Fun <$> get
        3 -> PrExHole <$> get
        4 -> UnOp <$> get <*> get
        5 -> BinOp <$> get <*> get <*> get
        6 -> App <$> get <*> get
        7 -> Quant <$> get <*> get <*> get <*> get
        8 -> Paren <$> get
        _ -> fail $ "SerializeErr (PreExpr' a) " ++ show tag_

type PreExpr = PreExpr' Variable

instance Functor PreExpr' where
    fmap f (Var a) = Var $ f a
    fmap _ (Con c) = Con c
    fmap _ (Fun g) = Fun g
    fmap _ (PrExHole h) = PrExHole h
    fmap f (UnOp op e) = UnOp op $ fmap f e
    fmap f (BinOp op e e') = BinOp op (fmap f e) (fmap f e')
    fmap f (App e e') = App (fmap f e) (fmap f e')
    fmap f (Quant q a e e') = Quant q (f a) (fmap f e) (fmap f e')
    fmap f (Paren e) = Paren $ fmap f e

-- | Instancia arbitrary para las preExpresiones.
instance Arbitrary PreExpr where
    arbitrary =
        oneof [   Var <$> arbitrary
                , Con <$> arbitrary
                , Fun <$> arbitrary
                , PrExHole <$> arbitrary
                , UnOp <$> arbitrary <*> arbitrary
                , BinOp <$> arbitrary <*> arbitrary <*> arbitrary
                , App <$> arbitrary <*> arbitrary
                , Quant <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
                , Paren <$> arbitrary
                ]

-- | Pretty print para las preExpresiones.
instance Show PreExpr where
    show (Var x) = show x
    show (Con k) = show k
    show (Fun f) = show f
    show (PrExHole h) = show h
    show (UnOp op preExp) = show op ++ " " ++ show preExp
    show (BinOp op preExp0 preExp1) = show preExp0 ++ show op ++ show preExp1
    show (App preExp0 preExp1) = show preExp0 ++ "@" ++ show preExp1
    show (Quant qua v preExp0 preExp1) = "〈" ++ show qua ++ show v ++ ":" 
                                        ++ show preExp0 ++ ":" 
                                        ++ show preExp1 ++ "〉"
    show (Paren e) = "(" ++ show e ++ ")"


-- | Substitucion de variable por variable en preExpresiones.
-- PRE = { v' variable fresca para pe }
substitution :: Eq a => a -> a -> PreExpr' a -> PreExpr' a
substitution v v' e = substVar v v' <$> e
    where substVar w w' w'' | w == w'' = w'
                            | otherwise = w''
