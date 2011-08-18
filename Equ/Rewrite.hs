module Equ.Rewrite where

import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Text as T

import Equ.PreExpr.Internal
import Equ.Syntax
import Equ.Rule
import Equ.Expr

type ExprSubst = M.Map Variable PreExpr


match :: PreExpr -> PreExpr -> ExprSubst -> Maybe ExprSubst
-- [match v -> e] U s = si s(v) es algo distinto de e, entonces no hay matching.
match (Var v) e s = if e==(Var v)
                       then Just s
                       else case M.lookup v s of
                                Nothing -> Just $ M.union s $ M.insert v e M.empty
                                      
                                Just f -> if e==f
                                            then Just s
                                            else Nothing

match (UnOp op1 e1) (UnOp op2 e2) s = if op1==op2
                                         then match e1 e2 s
                                         else Nothing

match (BinOp op1 e1 e2) (BinOp op2 f1 f2) s = if op1==op2
                                                 then match e1 f1 s >>= \t -> match e2 f2 t
                                                 else Nothing
    
match (App e1 e2) (App f1 f2) s = match e1 f1 s >>= \t -> match e2 f2 t
                                                        
match (Paren e) (Paren f) s = match e f s
{- Las expresiones (x) y x deberian poder matchearse?
    Lo mismo con otras similares
-}
match (Paren e1) e2 s = match e1 e2 s
match e1 (Paren e2) s = match e1 e2 s

   
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
    
match (Quant q v e1 e2) (Quant p w f1 f2) s =
    if q==p
       then if v==w
           -- Si tenemos la misma variable cuantificada, entonces realizamos el match en las subexpresiones
                then match e1 f1 s >>= \t -> match e2 f2 t
            -- Si no, tenemos que reemplazar la variable cuantificada de la primera expresion, por la de la segunda,
            -- pero cuidando de no capturar una variable libre, para eso aplicamos una sustitucion que pone una variable
            -- nueva
                else match e1 f1 s1 >>= \t -> match e2 f2 t
        else Nothing
    where s1 = M.insert v (Var w) (M.insert w (Var $ freshVar w (S.union (freeVars e1) (freeVars e2))) s)



match e1 e2 s | e1==e2 = Just s
              | otherwise = Nothing

-- Esta funcion devuelve todas las variables libres de una expresion
freeVars :: PreExpr -> S.Set Variable
freeVars (Var v) = S.insert v S.empty
freeVars (Con c) = S.empty
freeVars (Fun g) = S.empty
freeVars (PrExHole h) = S.empty
freeVars (UnOp op e) = freeVars e
freeVars (BinOp op e1 e2) = S.union (freeVars e1) (freeVars e2)
freeVars (App e1 e2) = S.union (freeVars e1) (freeVars e2)
freeVars (Quant q v e1 e2) = S.delete v $ S.union (freeVars e1) (freeVars e2)
freeVars (Paren e) = freeVars e

-- Esta funcion devuelve una variable fresca con respecto a un conjunto de variables
freshVar :: Variable -> S.Set Variable -> Variable
freshVar v s = firstNotIn s (infListVar v)
    where infListVar w = [Variable {varName= (T.pack . ((T.unpack $ varName w) ++) . show) n,
                                    varTy= varTy w} | n <- [(0::Int)..]]
          -- PRE: xs es infinita
          firstNotIn set xs | S.member (head xs) set = firstNotIn set $ tail xs
                            | otherwise = head xs

expr_rewrite :: Expr -> Rule -> Maybe Expr
expr_rewrite (Expr e) (Rule{lhs=Expr l,rhs=Expr r}) = match l e M.empty >>= \subst -> Just $ Expr $ applySubst subst r

-- Esta funcion es igua a la que hizo miguel en TypeChecker. Se puede escribir asi, ya que
-- PreExpr' es instancia de Monad
applySubst :: ExprSubst -> PreExpr -> PreExpr
applySubst s = (>>= (\v -> getSubstVar v s))

getSubstVar :: Variable -> ExprSubst -> PreExpr
getSubstVar v = M.findWithDefault (Var v) v
