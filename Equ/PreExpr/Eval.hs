module Equ.PreExpr.Eval where

import Equ.Syntax
import Equ.Theories.AbsName
import Equ.PreExpr.Symbols

import Equ.PreExpr.Internal
import Control.Applicative



semBinOp :: Operator -> Maybe (Int -> Int -> Int)
semBinOp op = case opName op of
                Sum -> Just (+)
                Prod -> Just (*)
                _ -> Nothing

semUnOp :: Operator -> Maybe (Int -> Int)
semUnOp op = case opName op of
               Succ -> Just (1+)
               _ -> Nothing

evalNat :: PreExpr -> Maybe Int
evalNat (Con c) = if conName c == Zero then Just 0 else Nothing
evalNat (UnOp op e) = semUnOp op <*> evalNat e
evalNat (BinOp op e e') = Nothing -- semBinOp op <*> evalNat e <*> evalNat e'
evalNat _ = Nothing


intToCon :: Int -> PreExpr
intToCon 0 = Con $ natZero
intToCon n = UnOp (natSucc) $ intToCon (n-1)


evalExpr :: PreExpr -> PreExpr
evalExpr (Var v) = Var v
evalExpr (Con c) = Con c
evalExpr (Fun f) = Fun f
evalExpr (PrExHole h) = PrExHole h
evalExpr e@(UnOp op e') = maybe (UnOp op (evalExpr e')) intToCon $ evalNat e
evalExpr (BinOp op e1 e2) = case (evalNat e1, evalNat e2) of
                              (Nothing,Nothing) ->  BinOp op (evalExpr e1) (evalExpr e2)
                              (Just e', Nothing) -> BinOp op (intToCon e') (evalExpr e2)
                              (Nothing, Just e') -> BinOp op (evalExpr e1) (intToCon e')
                              (Just e',Just e'') -> BinOp op (intToCon e') (intToCon e'')
evalExpr (App e e') = App (evalExpr e) (evalExpr e')
evalExpr (Quant q v r t) = Quant q v (evalExpr r) (evalExpr t)
evalExpr (Paren e) = Paren (evalExpr e)