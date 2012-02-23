{-# LANGUAGE TypeSynonymInstances #-}
module Equ.PreExpr.Show where

import Equ.Syntax
import Equ.PreExpr.Internal
import Equ.PreExpr.Eval
import Equ.Theories.AbsName
-- import Control.Applicative ((<$>), (<*>),Applicative(..))

-- data PreExpr' a = Var a
--                 | Con Constant
--                 | Fun Func
--                 | PrExHole Hole
--                 | UnOp Operator (PreExpr' a)
--                 | BinOp Operator (PreExpr' a) (PreExpr' a)
--                 | App (PreExpr' a) (PreExpr' a)
--                 | Quant Quantifier a (PreExpr' a) (PreExpr' a)
--                 | Paren (PreExpr' a)
--                   deriving Eq


showL :: PreExpr -> String -> Maybe String
showL (Con c) xs = if conName c == Empty then Just $ "[" ++ xs ++ "]"
                      else Nothing
showL (BinOp op e e') xs = if opName op == Append 
                           then showL e' (xs' ++ showExpr e)
                           else Nothing
    where xs' = if null xs then xs else xs ++ ","
showL _ _ = Nothing
                                  

showExpr :: PreExpr -> String
showExpr (Var x) = show x
showExpr (Con k) = show k
showExpr (Fun f) = show f
showExpr (PrExHole h) = show h
showExpr e@(UnOp op e') = case evalNat e of
                         Nothing -> show op ++ " " ++ showExpr e'
                         Just n -> show n
showExpr l@(BinOp op e e') = case showL l "" of 
                               Nothing -> case (evalNat e, evalNat e') of
                                 (Nothing, Nothing) -> showExpr e ++  " " ++ show op ++ " " ++ showExpr e'
                                 (Just n,Nothing) -> show n ++ " " ++ show op ++ " " ++ showExpr e'
                                 (Nothing, Just n) -> showExpr e ++ " " ++ show op ++ " " ++ show n
                                 (Just m,Just n) ->  show m ++ " " ++ show op ++ " " ++ show n
                               Just l' -> l'
showExpr (App e e') = case evalNat e' of
                        Nothing -> showExpr e ++ "@" ++ showExpr e'
                        Just n ->  showExpr e ++ "@" ++ show n
showExpr (Quant q v r t) = "〈" ++ show q ++ show v ++ ":" 
                           ++ showExpr r ++ ":" 
                           ++ showExpr t ++ "〉"
showExpr (Paren e) = "(" ++ showExpr e ++ ")"


