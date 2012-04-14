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
     show p = showExpr' p
--     show (Var x) = show x
--     show (Con k) = show k
--     show (Fun f) = show f
--     show (PrExHole h) = show h
--     show (UnOp op preExp) = show op ++ " " ++ show preExp
--     show (BinOp op preExp0 preExp1) = show preExp0 ++ show op ++ show preExp1
--     show (App preExp0 preExp1) = show preExp0 ++ "@" ++ show preExp1
--     show (Quant qua v preExp0 preExp1) = "〈" ++ show qua ++ show v ++ ":" 
--                                         ++ show preExp0 ++ ":" 
--                                         ++ show preExp1 ++ "〉"
--     show (Paren e) = "(" ++ show e ++ ")"
    
    
    
showExpr' :: PreExpr -> String
showExpr' (BinOp op e1 e2) =
            let (izq,der)=(showWithParentsBin e1 op,showWithParentsBin e2 op) in
                izq ++ show op ++ der
                
    where showWithParentsBin e oper = case e of
           (BinOp op' _ _) -> if opPrec oper >= opPrec op'
                                    then "("++showExpr' e++")"
                                    else showExpr' e
           otherwise -> showExpr' e
           
showExpr' (UnOp op e) =
                let down = showWithParentsUn e op in
                    show op ++ " "++down
                    
    where showWithParentsUn e oper = case e of
            (BinOp _ _ _) -> "("++showExpr' e++")"
            (App _ _) -> "("++showExpr' e++")"
            (Quant _ _ _ _) -> "(" ++ showExpr' e++")"
            otherwise -> showExpr' e
                    
showExpr' (App e1 e2) = showExpr' e1 ++ "@" ++ showExpr' e2
showExpr' (Quant q v e1 e2) = "〈" ++ show q ++ show v ++ ":" 
                                        ++ showExpr' e1 ++ ":" 
                                        ++ showExpr' e2 ++ "〉"
showExpr' (Paren e) = "(" ++ showExpr' e ++ ")"
showExpr' (Var x) = show x
showExpr' (Con k) = show k
showExpr' (Fun f) = show f
showExpr' (PrExHole h) = show h

{-- | Funcion que, dada una PreExpr, elimina las expresiones "Paren" que son necesarias
    para desambiguar expresiones. Ejemplo:
    unParen ( Paren ( or (Paren $ equiv p q) r ) ) = Paren ( or ( equiv p q ) r )
    El parentesis que estaba en la expresión (equiv p q) fue necesario introducirlo
    para poder diferenciar la expresión " or (equiv p q) r " de la expresión
    equiv p (or (q r)).
    --}
unParen :: PreExpr -> PreExpr
unParen (BinOp op e1 e2) = BinOp op (checkParen e1 op) (checkParen e2 op)
    where checkParen e o = case e of
            (Paren (BinOp op_e e1' e2')) -> if opPrec o >= opPrec op_e
                                                then BinOp op_e (unParen e1') (unParen e2')
                                                else unParen e
            otherwise -> unParen e
            
unParen (UnOp op e) = UnOp op (checkParen e op)
    where checkParen e' o = case e' of
            (Paren e'') -> case e'' of
                            (BinOp _ _ _) -> unParen e''
                            (App _ _) -> unParen e''
                            (Quant _ _ _ _) -> unParen e''  -- VER SI HACE FALTA ESTE CASO
                            otherwise -> unParen e'
            _ -> e'
unParen (App e1 e2) = App (unParen e1) (unParen e2)
unParen (Quant q v e1 e2) = Quant q v (unParen e1) (unParen e2)
unParen (Paren e) = Paren (unParen e)
unParen e = e



-- | Substitucion de variable por variable en preExpresiones.
-- PRE = { v' variable fresca para pe }
substitution :: Eq a => a -> a -> PreExpr' a -> PreExpr' a
substitution v v' e = substVar v v' <$> e
    where substVar w w' w'' | w == w'' = w'
                            | otherwise = w''
