-- | Las PreExpresiones son &#225;rboles de expresiones no necesariamente
-- tipables con huecos. Como se comenta en el m&#243;dulo Equ.Syntax, el
-- tipo que posiblemente puso el usuario est&#225; en las hojas del &#225;rbol.
{-# Language OverloadedStrings #-}
module Equ.PreExpr ( decode
                   , preExprHole
                   , isPreExprHole
                   , isPEHole
                   , placeHolderVar
                   , isPlaceHolderVar
                   , emptyExpr
                   , holePreExpr
                   , isPreExprParent
                   , isPreExprQuant
                   , listOfVar
                   , createPairs
                   , subExprQuant
                   , preExprApp
                   , quantVar
                   , termExpr
                   , rangeExpr
                   , exprApply
                   , prettyShow
                   , preExprIsQuant
                   , setTypeFocus
                   , checkIsAtom
                   , setAtomType
                   , setQuantType
                   , setVarQType
                   , glue -- TESTING!!
                   , module Equ.Syntax
                   , module Equ.PreExpr.Internal
                   , module Equ.PreExpr.Zipper
                   , module Equ.PreExpr.Monad
                   , module Equ.PreExpr.Subst
                   , FlatExpr(..)
                   , flat
                   ) 
    where

import Equ.Syntax(Variable(..), Operator(..), Constant(..), holeTy
                 , Quantifier (..), Func (..), var, HoleInfo, hole, Assoc(None))
import Equ.Types
import Equ.PreExpr.Internal
import Equ.PreExpr.Zipper
import Equ.PreExpr.Monad
import Equ.PreExpr.Subst
import Equ.PreExpr.Show
import Data.List (permutations)

import Data.Serialize(decode)
import Control.Arrow ((***))

isPEHole :: PreExpr -> Bool
isPEHole (PrExHole _) = True
isPEHole _ = False

-- | Dado un focus de una preExpresion, nos dice si esta es un hueco.
isPreExprHole :: Focus -> Bool
isPreExprHole = isPEHole . fst

isPreExprParent :: Focus -> Bool
isPreExprParent (Paren _,_) = True
isPreExprParent _ = False

isPreExprQuant :: Focus -> Bool
isPreExprQuant (Quant _ _ _ _, _) = True
isPreExprQuant _ = False

preExprIsQuant :: PreExpr -> Bool
preExprIsQuant (Quant _ _ _ _) = True
preExprIsQuant _ = False

-- | Creamos un hueco de preExpresion con informaci&#243;n.
preExprHole :: HoleInfo -> PreExpr
preExprHole i = PrExHole $ hole i

-- | En base a e1 y e2, creamos una preExpresion e1@e2
preExprApp :: PreExpr -> PreExpr -> PreExpr
preExprApp = App


-- | Funcion que devuelve la variable cuantificada en un cuantificador.
quantVar :: PreExpr -> Variable
quantVar (Quant _ v _ _) = v
quantVar _ = error "quantVar solo se aplica a expresiones cuantificadas"

-- | Funcion que devuelve la expresión Termino de una expresión cuantificada
termExpr :: PreExpr -> PreExpr
termExpr (Quant _ _ _ t) = t
termExpr _ = error "termExpr solo se aplica a expresiones cuantificadas"

rangeExpr :: PreExpr -> PreExpr
rangeExpr (Quant _ _ r _) = r
rangeExpr _ = error "rangeExpr solo se aplica a expresiones cuantificadas"

subExprQuant :: Focus -> Int
subExprQuant = (1+) . length . focusToFocuses . Just

-- | Una variable que el usuario no puede ingresar.
placeHolderVar :: Variable
placeHolderVar = var "" TyUnknown

isPlaceHolderVar :: Variable -> Bool
isPlaceHolderVar (Variable "" TyUnknown) = True
isPlaceHolderVar _ = False

-- | Un hueco sin información.
holePreExpr :: PreExpr
holePreExpr = preExprHole ""

emptyExpr :: Focus
emptyExpr = toFocus holePreExpr

-- | Dada una expresión @BinOp op e e'@ devuelve todas los
-- pares @(p,q)@ tal que @BinOp op e e' ~ BinOp op p q@, donde
-- @~@ significa igualdad modulo asociatividad. Si @op@ no es
-- asociativo, entonces devuelve el singleton @(e,e')@.
createPairs :: PreExpr -> [(PreExpr,PreExpr)]
createPairs e@(BinOp op _ _) = case opAssoc op of
                               None -> []
                               _ -> map split . glue op $ flatten op e
    where split (BinOp _ l r) =  (l,r)
          split _ = error "We cannot split with something different from a BinOp"
createPairs _ = error "We cannot split with something different from a BinOp"

-- | Lista de todos los nodos asociables.
flatten :: Operator -> PreExpr -> [PreExpr]
flatten o' e@(BinOp op l r) = if op == o' 
                              then flatten op l ++ flatten op r
                              else [e]
flatten _ e = [e]

-- | Reconstrucción de todas las formas de parsear una expresión con
-- un conectivo asociativo a partir de una lista de sus
-- subexpresiones asociables
glue :: Operator -> [PreExpr] -> [PreExpr]
glue _ [] = []
glue _ [e]    = return e
glue op [e,e'] = return $ BinOp op e e'
glue op es = 
    let ps = [splitAt i es | i <- [1..length es-1]]
    in
        concatMap (glue' op) ps
        
glue' :: Operator -> ([PreExpr],[PreExpr]) -> [PreExpr]
glue' op pss = 
    let (ps1',ps2') = (glue op *** glue op) pss
    in
        combine op ps1' ps2'
    where combine :: Operator -> [PreExpr] -> [PreExpr] -> [PreExpr]
          combine op ps ps' = foldl (\l e -> map (BinOp op e) ps' ++ l) [] ps
    
    {- asi estaba antes:
        concat [(uncurry (zipWith (BinOp op)) . (glue op *** glue op)) ps 
        | ps <- [splitAt i es | i <- [1..length es-1]]] -}


listOf :: Focus -> (Focus -> Bool) -> [Focus]
listOf f = flip filter (toFocuses $ toExpr f)

-- | Retorna una lista con las variables que aparecen en una expresión.
listOfVar :: Focus -> [Focus]
listOfVar = flip listOf isFocusVar
    where
        isFocusVar :: Focus -> Bool
        isFocusVar (Var _,_) = True
        isFocusVar _ = False


-- | Dada una variable y una lista de variables, devuelve la expresión aplicación
--   de la primera sobre todas las demás. exprApply f [x1,..,xn] = f@x1@..@xn
exprApply :: Variable -> [Variable] -> PreExpr
exprApply f vs = foldl (\e -> App e . Var) (Var f) vs
        
      
prettyShow :: PreExpr -> String
prettyShow = showExpr


-- | Dado un focus, un move y un tipo, cambiamos el tipo del focus al que 
-- nos mueve el move.
setAtomType :: Focus -> (Focus -> Focus) -> Type -> Focus
setAtomType f go ty = set ty (go f)
    where set :: Type -> Focus -> Focus
          set t (Var v,p) = (Var $ v {varTy = t},p)
          set t (Con c,p) = (Con $ c {conTy = t},p)
          set t (PrExHole h,p) = (PrExHole $ h {holeTy = t},p)
          set _ (_,_) = error "SetAtomType!"

setQuantType :: Focus -> (Focus -> Focus) -> Type -> Focus
setQuantType f go ty = goTop $ set ty (go f)
    where set :: Type -> Focus -> Focus
          set t (Quant q v e e',p) = (Quant (q {quantTy = t}) v e e',p)
          set _ _ = error "SetQuantType!"
          
setVarQType :: Focus -> (Focus -> Focus) -> Type -> Focus
setVarQType f go ty = goTop $ set ty (go f)
    where set :: Type -> Focus -> Focus
          set t (Quant q v e e',p) = (Quant q v{varTy = t} e e',p)
          set _ _ = error "SetVarQType!"

-- | Actualiza el tipo de todos los focus a los que nos mueve Move.
setTypeFocus :: [(Focus, Focus -> Focus)] -> Type -> Focus -> Focus
setTypeFocus [] _ f' = goTop f'
setTypeFocus ((_,go):fs) ty f' = setTypeFocus fs ty (goTop $ set ty (go f'))
    where set :: Type -> Focus -> Focus
          set t (UnOp op e, p) = (UnOp (op{opTy = t}) e,p)
          set t (BinOp op e e', p) = (BinOp (op{opTy = t}) e e',p)
          set _ _ = error "SetTypeFocus!"

-- | Checkea si un focus es un atomo de preExpresion.
checkIsAtom :: Focus -> Bool
checkIsAtom (Var _,_) = True
checkIsAtom (Con _,_) = True
checkIsAtom (PrExHole _,_) = True
checkIsAtom _ = False


-- | Flatten expresions.
data FlatExpr = FBin Operator [FlatExpr]
              | FVar Variable
              | FCon Constant
              | FUn Operator FlatExpr
              | FQuant Quantifier Variable FlatExpr FlatExpr
    deriving (Eq,Show)

{-
instance Eq FlatExpr where
    (FBin op1 fs1) == (FBin op2 fs2) = (op1 == op2) && (fs1 `elem` permutations fs2)
    (FVar v) == (FVar w) = v == w
    (FCon c1) == (FCon c2) = c1 == c2
    (FUn op1 fe1) == (FUn op2 fe2) = (op1 == op2) && (fe1 == fe2)
    (FQuant q1 v f1 g1) == (FQuant q2 w f2 g2) = (q1 == q2) && (v == w) &&
                                                 (f1 == f2) && (g1 == g2)
    _ == _ = False
-}
  
flat :: PreExpr -> FlatExpr 
flat (Var v)            = FVar v
flat (Con c)           = FCon c
flat (UnOp op pe)       = FUn op $ flat pe
flat (BinOp op pe pe')  = FBin op $ (flat' pe op) ++ (flat' pe' op)
flat (Quant q v pe pe') = FQuant q v (flat pe) (flat pe')
flat pe = error $ "Not implemented: flat of " ++ show pe

flat' :: PreExpr -> Operator -> [FlatExpr]
flat' pe@(BinOp op e e') op'
    | op == op' = flat' e op' ++ flat' e' op'
    | otherwise = [flat pe]
flat' pe _ = [flat pe]
