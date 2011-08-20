module Equ.Matching
    ( match
    , applySubst
    , ExprSubst
    )
    where

import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad

import Equ.Syntax
import Equ.Rule
import Equ.PreExpr
import Equ.Types

type ExprSubst = M.Map Variable PreExpr


whenM :: MonadPlus m => Bool -> m a -> m a
whenM True = id
whenM False = const mzero
  
whenML :: MonadPlus m => Bool -> a -> m a
whenML True = return
whenML False = const mzero

-- | Aplica una substitución a una expresión dada.
applySubst :: PreExpr -> ExprSubst -> PreExpr
applySubst (Var v) s = M.findWithDefault (Var v) v s
applySubst (UnOp op e) s = applySubst e s
applySubst (BinOp op e f) s = BinOp op (applySubst e s) (applySubst f s)
applySubst (App e f) s = App (applySubst e s) (applySubst f s)
applySubst (Quant q v e1 e2) s = Quant q v (applySubst e1 s) (applySubst e2 s)
applySubst (Paren e) s = Paren $ applySubst e s
applySubst e s = e

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
