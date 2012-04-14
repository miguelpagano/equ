{-# LANGUAGE TypeSynonymInstances #-}
module Equ.PreExpr.Show where

import Equ.Syntax
import Equ.PreExpr.Internal
import Equ.PreExpr.Eval
import Equ.PreExpr.Zipper
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
showExpr e@(UnOp op e') = 
    case evalNat e of
        Nothing -> let down = showWithParentsUn e' op in
                    show op ++ down
        Just n -> show n
        
    where showWithParentsUn e oper = case e of
            (BinOp _ _ _) -> "("++showExpr e++")"
            (App _ _) -> "("++showExpr e++")"
            (Quant _ _ _ _) -> "(" ++ showExpr e++")"
            otherwise -> showExpr e
        
showExpr l@(BinOp op e1 e2) = 
    case showL l "" of 
        Nothing -> let (izq,der)=(showWithParentsBin e1 op,showWithParentsBin e2 op) in
                        izq ++ show op ++ der
        Just l' -> l'
        
    where showWithParentsBin e oper = case e of
           (BinOp op' _ _) -> if opPrec oper >= opPrec op'
                                    then "("++showExpr e++")"
                                    else showExpr e
           otherwise -> showExpr e
           
showExpr (App e e') = showExpr e ++ "@" ++ showExpr e'
showExpr (Quant q v r t) = "〈" ++ show q ++ show v ++ ":" 
                           ++ showExpr r ++ ":" 
                           ++ showExpr t ++ "〉"
showExpr (Paren e) = "(" ++ showExpr e ++ ")"


