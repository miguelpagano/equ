{-# LANGUAGE TypeSynonymInstances,FlexibleInstances #-}
module Equ.PreExpr.Internal where

import Equ.Syntax
import Control.Applicative ((<$>), (<*>),Applicative(..))
import Test.QuickCheck(Arbitrary, arbitrary, oneof)

import Data.Serialize(Serialize, get, getWord8, put, putWord8)
import Control.Arrow ((***))
import qualified Data.Traversable as T
import Data.Foldable(foldMap)
import qualified Data.Foldable as F
import qualified Data.Monoid as M
import Data.Function (on)

data PreExpr' a = Var a
                | Con !Constant
                | PrExHole !Hole
                | UnOp !Operator (PreExpr' a)
                | BinOp !Operator (PreExpr' a) (PreExpr' a)
                | App (PreExpr' a) (PreExpr' a)
                | Quant !Quantifier a (PreExpr' a) (PreExpr' a)
                | Paren (PreExpr' a)
                | If (PreExpr' a) (PreExpr' a) (PreExpr' a)
                | Case (PreExpr' a) [((PreExpr' a),(PreExpr' a))]
                  deriving Eq

--  Instancia binary para PreExpr' a.
instance Serialize a => Serialize (PreExpr' a) where
    put (Var a) = putWord8 0 >> put a
    put (Con c) = putWord8 1 >> put c
    put (PrExHole h) = putWord8 3 >> put h
    put (UnOp op pe) = putWord8 4 >> put op >> put pe
    put (BinOp op pe pe') = putWord8 5 >> put op >> put pe >> put pe'
    put (App pe pe') = putWord8 6 >> put pe >> put pe'
    put (Quant q a pe pe') = putWord8 7 >> put q >> put a >> put pe >> put pe'
    put (Paren pe) = putWord8 8 >> put pe
    put (If c e1 e2) = putWord8 9 >> put c >> put e1 >> put e2
    put (Case e patterns) = putWord8 10 >> put e >> put patterns

    get = do
    tag_ <- getWord8
    case tag_ of
        0 -> Var <$> get
        1 -> Con <$> get
        3 -> PrExHole <$> get
        4 -> UnOp <$> get <*> get
        5 -> BinOp <$> get <*> get <*> get
        6 -> App <$> get <*> get
        7 -> Quant <$> get <*> get <*> get <*> get
        8 -> Paren <$> get
        9 -> If <$> get <*> get <*> get
        10 -> Case <$> get <*> get
        _ -> fail $ "SerializeErr (PreExpr' a) " ++ show tag_

type PreExpr = PreExpr' Variable

instance Functor PreExpr' where
    fmap f (Var a) = Var $ f a
    fmap _ (Con c) = Con c
    fmap _ (PrExHole h) = PrExHole h
    fmap f (UnOp op e) = UnOp op $ fmap f e
    fmap f (BinOp op e e') = BinOp op (fmap f e) (fmap f e')
    fmap f (App e e') = App (fmap f e) (fmap f e')
    fmap f (Quant q a e e') = Quant q (f a) (fmap f e) (fmap f e')
    fmap f (Paren e) = Paren $ fmap f e
    fmap f (If c e1 e2) = If (fmap f c) (fmap f e1) (fmap f e2)
    fmap f (Case e patterns) = Case (fmap f e) $ map (fmap f *** fmap f) patterns
    
instance F.Foldable PreExpr' where
    foldMap f (Var a) = f a 
    foldMap f (Con _) = M.mempty
    foldMap f (PrExHole _) = M.mempty
    foldMap f (UnOp _ e) = foldMap f e
    foldMap f (BinOp _ e e') = foldMap f e `M.mappend` foldMap f e'
    foldMap f (App e e')  = foldMap f e `M.mappend` foldMap f e'
    foldMap f (Quant q a e e') = f a `M.mappend` foldMap f e `M.mappend` foldMap f e'
    foldMap f (Paren e) = foldMap f e
    foldMap f (If c e1 e2) = foldMap f c `M.mappend` foldMap f e1 `M.mappend` foldMap f e2
    foldMap f (Case e ps) =  M.mconcat (foldMap f e:map (uncurry (M.mappend `on` foldMap f)) ps)


-- | Instancia arbitrary para las preExpresiones.
instance Arbitrary PreExpr where
    arbitrary =
        oneof [   Var <$> arbitrary
                , Con <$> arbitrary
                , PrExHole <$> arbitrary
                , UnOp <$> arbitrary <*> arbitrary
                , BinOp <$> arbitrary <*> arbitrary <*> arbitrary
                , App <$> arbitrary <*> arbitrary
                , Quant <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
                , Paren <$> arbitrary
                , If <$> arbitrary <*> arbitrary <*> arbitrary
                , Case <$> arbitrary <*> arbitrary
                ]

-- | Pretty print para las preExpresiones.
instance Show PreExpr where
     show = showExpr' 

-- | Pretty-printing con parentizado de expresiones.
showExpr' :: PreExpr -> String
showExpr' (BinOp op e1 e2) = showParentised op e1 ++ show op ++ showParentised op e2                
    where showParentised oper e = case e of
           (BinOp op' _ _) -> if opPrec oper >= opPrec op'
                             then "("++showExpr' e++")"
                             else showExpr' e
           _ -> showExpr' e
           
showExpr' (UnOp op e) = show op ++ " " ++ showParentised e 
    where showParentised e' = case e of
            (BinOp _ _ _) -> "(" ++ showExpr' e' ++ ")"
            (App _ _) -> "(" ++ showExpr' e' ++ ")"
            (Quant _ _ _ _) -> "(" ++ showExpr' e' ++ ")"
            _ -> showExpr' e'
                        
showExpr' (App e1 e2) = showExpr' e1 ++ "@" ++ showExpr' e2
showExpr' (Quant q v e1 e2) = "〈" ++ show q ++ show v ++ ":" 
                              ++ showExpr' e1 ++ ":" 
                              ++ showExpr' e2 ++ "〉"
showExpr' (Paren e) = "[PAREN](" ++ showExpr' e ++ ")"
showExpr' (Var x) = show x
showExpr' (Con k) = show k
showExpr' (PrExHole h) = show h
showExpr' (If c e1 e2) = "if " ++ showExpr' c ++ " then " ++ showExpr' e1 ++ " else " ++ showExpr' e2
showExpr' (Case e patterns) = "case " ++ showExpr' e ++ " of\n" ++ showPatterns patterns
    where showPatterns = unlines . map showPattern
          showPattern (p,e') = "\t" ++ showExpr' p ++ " -> " ++ showExpr' e'

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
                                           then unParen (BinOp op_e e1' e2')
                                           else unParen e
            (Paren (UnOp op_e e1')) -> if opPrec o >= opPrec op_e
                                          then unParen (UnOp op_e e1')
                                          else unParen e
            _ -> unParen e
            
unParen (UnOp op e) = UnOp op (checkParen e)
    where checkParen e' = case e' of
            (Paren e'') -> case e'' of
                            (BinOp _ _ _) -> unParen e''
                            (App _ _) -> unParen e''
                            (Quant _ _ _ _) -> unParen e''  -- VER SI HACE FALTA ESTE CASO
                            (UnOp _ _) -> unParen e''
                            _ -> unParen e'
            _ -> e'
unParen (App e1 e2) = App (unParen e1) (unParen e2)
unParen (Quant q v e1 e2) = Quant q v (unParen e1) (unParen e2)
unParen (Paren e) = Paren (unParen e)
unParen (If c e1 e2) = If (unParen c) (unParen e1) (unParen e2)
unParen (Case e patterns) = Case (unParen e) (unParenAll patterns)
    where unParenAll ps = map (unParen *** unParen) ps
unParen e = e



-- | Substitucion de variable por variable en preExpresiones.
-- PRE = { v' variable fresca para pe }
substitution :: Eq a => a -> a -> PreExpr' a -> PreExpr' a
substitution v v' e = substVar v v' <$> e
    where substVar w w' w'' | w == w'' = w'
                            | w /= w'' = w''


          
-- Esta funcion toma una expresión que es un operador aplicado y retorna el operador.
-- Si se le pasa una expresión de otro tipo, es indefinida.
getOperator :: PreExpr' a -> Maybe Operator
getOperator (UnOp op _) = Just op
getOperator (BinOp op _ _) = Just op
getOperator _ = Nothing

getConstant :: PreExpr' a -> Maybe Constant
getConstant (Con c) = Just c
getConstant _ = Nothing

isVar :: a -> PreExpr' b -> Either a b
isVar _ (Var x) = Right x
isVar a _ = Left a
