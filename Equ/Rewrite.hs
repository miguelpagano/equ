module Equ.Rewrite
    ( match
    , exprRewrite
    )
    where

import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Text as T
import Control.Monad

import Equ.PreExpr.Internal
import Equ.Syntax
import Equ.Rule
import Equ.Expr
import Equ.Types

type ExprSubst = M.Map Variable PreExpr

whenM :: MonadPlus m => Bool -> m a -> m a
whenM True = id
whenM False = const mzero
  
whenML :: MonadPlus m => Bool -> a -> m a
whenML True = return
whenML False = const mzero

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


{- Función que implementa el algoritmo de matching. Toma una lista de variables
que están ligadas a algún cuantificador, una expresión patrón, otra expresión y
un mapa de sustituciones. 
-}
match' :: [Variable] -> PreExpr -> PreExpr -> ExprSubst -> Maybe ExprSubst

{- El caso principal del algoritmo, donde el patrón es una variable. 
* Si la expresión e' es igual al patrón Var v, se devuelve el mismo mapa de 
sustituciones (es decir, no hay que reemplazar nada para llegar desde una 
expresión a la otra).
* Si las expresiones son distintas y v pertenece bvs, entonces no hay matching.
(para que dos expresiones cuantificadas matcheen, se considera a sus variables 
ligadas como la misma variable, y es la que se agrega a la lista bvs, por eso 
no hay matching entre una de esas variables y cualquier otra cosa distinta).
* Si las expresiones son distintas y v no pertenece a bvs, nos fijamos si en el 
mapa de sustituciones se encuentra la variable. Si no, entonces podemos matchear
v por e'. Si v está en el mapa, entonces para que haya matching tiene que estar 
asociada con la expresión e'.
-}
match' bvs e@(Var v) e' s | e == e' = return s
                         | v `elem` bvs = mzero
                         | otherwise = maybe (return $ M.insert v e' s)
                                             (\f -> whenML (e' == f) s)
                                             $ M.lookup v s

match' bvs (UnOp op1 e1) (UnOp op2 e2) s = whenM (op1==op2) $ match' bvs e1 e2 s

match' bvs (BinOp op1 e1 e2) 
          (BinOp op2 f1 f2) s = whenM (op1==op2) $ match' bvs e1 f1 s >>= 
                                                 match' bvs e2 f2
    
match' bvs (App e1 e2) (App f1 f2) s = match' bvs e1 f1 s >>= match' bvs e2 f2 

match' bvs (Paren e1) e2 s = match' bvs e1 e2 s
match' bvs e1 (Paren e2) s = match' bvs e1 e2 s

{-
Para matchear dos expresiones cuantificadas, deben ser el mismo cuantificador.
Si las variables cuantificadas v y w son la misma, entonces hacemos matching en 
las subexpresiones, agregando v a la lista de variables ligadas bvs.
Si v/=w, entonces reemplazamos v y w por una variable fresca en ambas expresiones
y luego realizamos matching en las subexpresiones, agregando la variable fresca
a bvs.
-}    
match' bvs (Quant q v e1 e2) (Quant p w f1 f2) s =
    whenM (q==p) $
        if v==w then match' (v:bvs) e1 f1 s >>= match' (v:bvs) e2 f2
                else match' (fv:bvs) (subst v fv e1) (subst w fv f1) s >>=
                     match' (fv:bvs) (subst v fv e2) (subst w fv f2)
    where fv= freshVar $ S.unions [freeVars $ Var v,freeVars $ Var w,
                                   freeVars e1, freeVars e2,freeVars f1, 
                                   freeVars f2]
          subst = substitution

-- Si no estamos en ningun caso anterior, entonces solo hay matching
-- si las expresiones son iguales.
match' bvs e1 e2 s = whenML (e1==e2) s

{-| match toma una expresión patrón y otra que quiere matchearse con el patrón.
Si hay matching, retorna el mapa de sustituciones que deben realizarse
simultáneamente para llegar desde la expresión patrón a la expresión dada.
-}
match :: PreExpr -> PreExpr -> Maybe ExprSubst
match e e' = match' [] e e' M.empty

{- | Dada una expresión y una regla, si la expresión matchea con el lado
izquierdo de la regla, entonces se reescribe de acuerdo al lado derecho
de la regla.
-}
exprRewrite :: Expr -> Rule -> Maybe Expr
exprRewrite (Expr e) (Rule{lhs=Expr l,rhs=Expr r}) = match l e >>= 
                                    \subst -> Just $ Expr $ applySubst subst r
