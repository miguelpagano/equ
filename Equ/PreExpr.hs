-- | Las PreExpresiones son &#225;rboles de expresiones no necesariamente
-- tipables con huecos. Como se comenta en el m&#243;dulo Equ.Syntax, el
-- tipo que posiblemente puso el usuario est&#225; en las hojas del &#225;rbol.
{-# Language OverloadedStrings #-}
module Equ.PreExpr ( freeVars, freshVar
                   , encode, decode
                   , preExprHole, isPreExprHole
                   , placeHolderVar
                   , isPlaceHolderVar
                   , emptyExpr, holePreExpr
                   , agrupOp, agrupNotOp, checkIsAtom, opOfFocus
                   , setType, updateOpType, setAtomType
                   , module Equ.Syntax
                   , module Equ.PreExpr.Internal
                   , module Equ.PreExpr.Zipper
                   , module Equ.PreExpr.Monad
                   , module Equ.PreExpr.Subst
                   ) 
    where


import Equ.Syntax(Variable(..), Operator(..), Constant(..), holeTy
                 , Quantifier, var, HoleInfo, hole)
import Data.Set (Set,union,delete,empty,insert,member)
import Equ.Types
import Equ.PreExpr.Internal
import Equ.PreExpr.Zipper
import Equ.PreExpr.Monad
import Equ.PreExpr.Subst

import Data.Text(pack)
import Data.Serialize(encode, decode)


-- | Dado un focus de una preExpresion, nos dice si esta es un hueco.
-- import Equ.Parser
import Equ.Theories.AbsName

isPreExprHole :: Focus -> Bool
isPreExprHole (PrExHole _, _) = True
isPreExprHole _ = False

-- | Creamos un hueco de preExpresion con informaci&#243;n.
preExprHole :: HoleInfo -> PreExpr
preExprHole i = PrExHole $ hole i

-- | Esta funci&#243;n devuelve todas las variables libres de una expresion
freeVars :: PreExpr -> Set Variable
freeVars (Var v) = insert v empty
freeVars (Con _) = empty
freeVars (Fun _) = empty
freeVars (PrExHole _) = empty
freeVars (UnOp _ e) = freeVars e
freeVars (BinOp _ e1 e2) = freeVars e1 `union` freeVars e2
freeVars (App e1 e2) = freeVars e1 `union` freeVars e2
freeVars (Quant _ v e1 e2) = delete v $ freeVars e1 `union` freeVars e2
freeVars (Paren e) = freeVars e

-- | Esta funci&#243;n devuelve una variable fresca con respecto a un conjunto de variables
freshVar :: Set Variable -> Variable
freshVar s = firstNotIn s infListVar
    where infListVar = [var (pack $ "v" ++ show n) TyUnknown | n <- [(0::Int)..]]
          -- PRE: xs es infinita
          firstNotIn set xs | head xs `member` set = firstNotIn set $ tail xs
                            | otherwise = head xs

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

-- Dada una lista de Focus, filtra los que no son operadores de preExpresion.
genListOfOp :: [(Focus, Focus -> Focus)] -> [(Focus, Focus -> Focus)]
genListOfOp lf = filter (\((pe,_),_) -> case pe of
                             UnOp _ _ -> True
                             BinOp _ _ _ -> True
                             _ -> False) lf

-- | Retorna el operador de preExpresion de un focus o Nothing.
opOfFocus :: (Focus, Focus -> Focus) -> Maybe Operator
opOfFocus ((UnOp op _,_),_) = Just $ op {opTy = TyUnknown}
opOfFocus ((BinOp op _ _,_),_) = Just $ op {opTy = TyUnknown}
opOfFocus _ = Nothing

-- Checkea si un focus es un operador de preExpresion.
checkIsOp :: (Focus, Focus -> Focus) -> Bool
checkIsOp = maybe False (const True) . opOfFocus

-- | Checkea si un focus es un atomo de preExpresion.
checkIsAtom :: Focus -> Bool
checkIsAtom (Var _,_) = True
checkIsAtom (Con _,_) = True
checkIsAtom (PrExHole _,_) = True
checkIsAtom _ = False

-- | Dado un focus, un move y un tipo, cambiamos el tipo del focus al que 
-- nos mueve el move.
setAtomType :: Focus -> (Focus -> Focus) -> Type -> Focus
setAtomType f go t = goTop $ set t (go f)
    where
        set :: Type -> Focus -> Focus
        set t (Var v,p) = (Var $ v {varTy = t},p)
        set t (Con c,p) = (Con $ c {conTy = t},p)
        set t (PrExHole h,p) = (PrExHole $ h {holeTy = t},p)

-- | Filtra todos los focus que son operadores de preExpresion.
agrupNotOp :: [(Focus, Focus -> Focus)] -> [(Focus, Focus -> Focus)]
agrupNotOp = filter (\f -> opOfFocus f == Nothing)

-- | Filtra todos los focus que son operadores de preExpresion. 
agrupOp :: [(Focus, Focus -> Focus)] -> [[(Focus, Focus -> Focus)]]
agrupOp = agrupOp' . genListOfOp

agrupOp' :: [(Focus, Focus -> Focus)] -> [[(Focus, Focus -> Focus)]]
agrupOp' [] = []
agrupOp' lf = take': agrupOp' drop'
    where
        take' = takeWhile (\f -> (opOfFocus f == (opOfFocus . head) lf)) lf
        drop' = dropWhile (\f -> (opOfFocus f == (opOfFocus . head) lf)) lf

-- | Actualiza el tipo de todos los focus a los que nos mueve Move.
setType :: [(Focus, Focus -> Focus)] -> Type -> Focus -> Focus
setType [] _ f' = goTop f'
setType ((_,go):fs) t f' = setType fs t (set t (go f'))
    where set :: Type -> Focus -> Focus
          set t (UnOp op e, p) = (UnOp (op{opTy = t}) e,p)
          set t (BinOp op e e', p) = (BinOp (op{opTy = t}) e e',p)
          
-- | Actualiza el tipo de una lista de Focus.
updateOpType :: [(Focus, Focus -> Focus)] -> Type -> [(Focus, Focus -> Focus)]
updateOpType [] _ = []
updateOpType ((f,go):fs) t = ((set t f), go) : updateOpType fs t
    where set :: Type -> Focus -> Focus
          set t (UnOp op e, p) = (UnOp (op{opTy = t}) e,p)
          set t (BinOp op e e', p) = (BinOp (op{opTy = t}) e e',p)
