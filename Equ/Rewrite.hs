module Equ.Rewrite where

import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Text as T

import Equ.PreExpr.Internal
import Equ.Syntax
import Equ.Rule
import Equ.Expr
import Equ.Types

type ExprSubst = M.Map Variable PreExpr


match :: [Variable] -> PreExpr -> PreExpr -> ExprSubst -> Maybe ExprSubst
-- [match v -> e] U s = si s(v) es algo distinto de e, entonces no hay matching.
match bvs e@(Var v) e' s | e == e' = Just s
                         | v `elem` bvs = Nothing
                         | otherwise =
                            case M.lookup v s of
                                Nothing -> Just $ M.insert v e' s
                                Just f -> if e' == f then Just s else Nothing


match bvs (UnOp op1 e1) (UnOp op2 e2) s = if op1==op2
                                            then match bvs e1 e2 s
                                            else Nothing

match bvs (BinOp op1 e1 e2) (BinOp op2 f1 f2) s = if op1==op2
                                                    then match bvs e1 f1 s >>= \t -> match bvs e2 f2 t
                                                    else Nothing
    
match bvs (App e1 e2) (App f1 f2) s = match bvs e1 f1 s >>= \t -> match bvs e2 f2 t

match bvs (Paren e1) e2 s = match bvs e1 e2 s
match bvs e1 (Paren e2) s = match bvs e1 e2 s

-- CUANTIFICADORES
{- EJEMPLO INSPIRADOR:
    queremos matchear con la expresion: E1= <∀x : x = z : F@x>, la expresion E2= <∀z : z = F@a : F@z>
    Lo primero que deberiamos hacer es sustituir x por z en E1. Pero al hacer esto, vemos que se nos captura
    una variable que era libre. Por lo tanto, primero deberiamos reemplazar z por una NUEVA variable en E1.
    Si hacemos eso, entonces, primero nos queda la substitucion z->v_new:
    <∀x : x = v_new : F@x>
    luego, sustituimos x por z:
    <∀z : z = v_new : F@z>
    y ahora aplicamos match a las expresiones rango y termino del cuantificador, con lo cual obtendriamos la sustitucion
    v_new -> F@a.
-}
    
match bvs (Quant q v e1 e2) (Quant p w f1 f2) s =
    if q==p
       then if v==w
                -- Si tenemos la misma variable cuantificada, entonces realizamos el match en las subexpresiones
                then match (v:bvs) e1 f1 s >>= \t -> match (v:bvs) e2 f2 t
                -- Si no, tenemos que reemplazar la variable cuantificada de la primera expresion, por la de la segunda,
                -- pero cuidando de no capturar una variable libre, para eso aplicamos una sustitucion que pone una variable
                -- nueva
                else match (fv:bvs) (substitution v fv e1) (substitution w fv f1) s >>=
                     \t -> match (fv:bvs) (substitution v fv e2) (substitution w fv f2) t
        else Nothing
    where fv= freshVar $ S.unions [freeVars $ Var v,freeVars $ Var w, freeVars e1, freeVars e2,
                                   freeVars f1, freeVars f2]


match bvs e1 e2 s | e1==e2 = Just s
                  | otherwise = Nothing


-- Esta funcion devuelve todas las variables libres de una expresion
freeVars :: PreExpr -> S.Set Variable
freeVars (Var v) = S.insert v S.empty
freeVars (Con c) = S.empty
freeVars (Fun g) = S.empty
freeVars (PrExHole h) = S.empty
freeVars (UnOp op e) = freeVars e
freeVars (BinOp op e1 e2) = freeVars e1 `S.union` freeVars e2
freeVars (App e1 e2) = freeVars e1 `S.union` freeVars e2
freeVars (Quant q v e1 e2) = freeVars e1 `S.union` freeVars e2
freeVars (Paren e) = freeVars e

-- Esta funcion devuelve una variable fresca con respecto a un conjunto de variables
-- Necesito la variable para mantener el tipo.
freshVar :: S.Set Variable -> Variable
freshVar s = firstNotIn s infListVar
    where infListVar = [Variable {varName= (T.pack . ("v" ++) . show) n,
                                    varTy= TyUnknown} | n <- [(0::Int)..]]
          -- PRE: xs es infinita
          firstNotIn set xs | S.member (head xs) set = firstNotIn set $ tail xs
                            | otherwise = head xs

exprRewrite :: Expr -> Rule -> Maybe Expr
exprRewrite (Expr e) (Rule{lhs=Expr l,rhs=Expr r}) = match [] l e M.empty >>= \subst -> Just $ Expr $ applySubst subst r

-- Esta funcion es igua a la que hizo miguel en TypeChecker. Se puede escribir asi, ya que
-- PreExpr' es instancia de Monad
applySubst :: ExprSubst -> PreExpr -> PreExpr
applySubst s (Var v) = M.findWithDefault (Var v) v s
applySubst s (UnOp op e) = applySubst s e
applySubst s (BinOp op e f) = BinOp op (applySubst s e) (applySubst s f)
applySubst s (App e f) = App (applySubst s e) (applySubst s f)
applySubst s (Quant q v e1 e2) = Quant q v (applySubst s e1) (applySubst s e2)
applySubst s (Paren e) = Paren $ applySubst s e
applySubst s e = e
