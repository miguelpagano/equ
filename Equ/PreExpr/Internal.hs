{-# LANGUAGE TypeSynonymInstances #-}
module Equ.PreExpr.Internal where

import Equ.Syntax
import Data.Monoid
import Data.Foldable (Foldable(..))
import qualified Data.Foldable as F
import Control.Applicative ((<$>), (<*>),Applicative(..))
import Test.QuickCheck(Arbitrary, arbitrary, oneof)

{- Propiedades de PreExpresiones (QC): queremos poder respetar la forma
   de escribir una expresión.
   
    * 'pretty . parser = id'
    * 'parser . pretty = id'
-}

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

type PreExpr = PreExpr' Variable

instance Monad PreExpr' where
    return a = Var a
    Var v >>= f = f v
    Con c >>= _ = Con c
    Fun f >>= _ = Fun f
    PrExHole h >>= _ = PrExHole h
    -- quise escribir todos los casos que siguen asi, pero no compila:
    --e >>= f = fmap (>>= f) e
    UnOp op e >>= f = UnOp op (e >>= f)
    BinOp op e1 e2 >>= f = BinOp op (e1 >>= f) (e2 >>= f)
    App e1 e2 >>= f = App (e1 >>= f) (e2 >>= f)
    Quant q v e1 e2 >>= f = let (Var v') = f v in Quant q v' (e1 >>= f) (e2 >>= f)
    Paren e >>= f = Paren (e >>= f)

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

instance Monad PreExpr' where
    return a = Var a
    Var v >>= f = f v
    Con c >>= _ = Con c
    Fun f >>= _ = Fun f
    PrExHole h >>= _ = PrExHole h
    -- quise escribir todos los casos que siguen asi, pero no compila:
    --e >>= f = fmap (>>= f) e
    UnOp op e >>= f = UnOp op (e >>= f)
    BinOp op e1 e2 >>= f = BinOp op (e1 >>= f) (e2 >>= f)
    App e1 e2 >>= f = App (e1 >>= f) (e2 >>= f)
    --Quant q v e1 e2 >>= f = Quant q v (e1 >>= f) (e2 >>= f)
    Paren e >>= f = Paren (e >>= f)

instance Foldable PreExpr' where
    foldMap f (Var v) = f v
    foldMap f (UnOp _ e) = foldMap f e
    foldMap f (BinOp _ e e') = foldMap f e `mappend` foldMap f e'
    foldMap f (App e e') = foldMap f e `mappend` foldMap f e'
    foldMap f (Quant q v e e') = f v `mappend` foldMap f' e `mappend` foldMap f' e'
        where f' w = f w 
--                   | v == w = mempty
--                   | otherwise = f w
    foldMap _ (PrExHole _) = mempty
    foldMap f (Paren e) = foldMap f e

{-
instance Applicative PreExpr' where
    pure = Var
    Var f <*> Var v = Var $ f v
    f <*> UnOp op e = UnOp op $ f <*> e
    f <*> BinOp op e e' = BinOp op (f <*> e) (f <*> e')
    f <*> App e e' = App (f <*> e) (f <*> e')
    f <*> Quant q v e e' = Quant 
    _ <*> (Con c) = Con c
    _ <*> (Fun g) = Fun g
    _ <*> (PrExHole h) = PrExHole h
{-    
    fmap f (BinOp op e e') = BinOp op (fmap f e) (fmap f e')
    fmap f (App e e') = App (fmap f e) (fmap f e')
    fmap f (Quant q a e e') = Quant q (f a) (fmap f e) (fmap f e')
    fmap f (Paren e) = Paren $ fmap f e
-}
-}



-- | Instancia arbitrary para las preExpresiones, lo único que dejamos fijo es el 
-- operador unario, esto para simplificar la forma de las preExpresiones.
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
    show (UnOp op preExp) = show op ++ "(" ++ show preExp ++ ")"
    show (BinOp op preExp0 preExp1) = "(" ++ show preExp0 ++ ")" ++ show op ++ 
                                      "(" ++ show preExp1 ++ ")"
    show (App preExp0 preExp1) = show preExp0 ++ " " ++ "(" ++ show preExp1 ++ ")"
    show (Quant qua v preExp0 preExp1) = show qua ++ show v ++ " in " 
                                        ++ show preExp0 ++ " | " 
                                        ++ show preExp1
    show (Paren e) = "〔" ++ show e ++ " 〕"
