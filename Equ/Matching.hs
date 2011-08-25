module Equ.Matching
    ( match
    , applySubst
    , ExprSubst
    , MatchError (..)
    )
    where

import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad

import Equ.PreExpr

type ExprSubst = M.Map Variable PreExpr

{- COSAS QUE ME QUEDARON EN EL AIRE:
    Me cruce con un problema parecido al que paso con las variables al
    compararlas, es decir, para las variables cambiamos la instancia de Eq
    para que la comparación solamente tenga en cuenta el representante. Ahora
    habría que hacer esto misma para las funciones y las constantes?
    Usamos la comparacion para ver que si dos nombre de función o de constante
    son distintos entonces no existe maching.
-}

-- | Posibles errores al hacer matching.
data MatchError = DoubleMatch Variable PreExpr PreExpr
                | BindingVar Variable
                | InequPreExpr PreExpr PreExpr
                | InequOperator Operator Operator
                | InequQuantifier Quantifier Quantifier
                
                {-
                | InequQuant        -- Cuantificadores distintos.
                | FuncWithVar       -- F(..) |-> x
                | ConstWithVar      -- C |-> x
                | DoubleMatch       -- x |-> t con x |-> t' y t != t'
                | BindingVar        -- v se encuentra en bvs.
                | InequPreExpr PreExpr PreExpr-}
                deriving (Show, Eq)
                
inequExprError :: PreExpr -> PreExpr -> MatchError
inequExprError e1 e2 = InequPreExpr e1 e2

{- WhenM y whenML.
    Para un valor de verdad y un error particular; 
        True => seguir la computación.
        False => devolver el error particular.
-}
{-
    Para intentar usar when* sin cambiar demasiado hice que MatchError
    fuera instancia de Error para usar la MonadPlus Either Error, pero 
    despues me parecio que era demasiado para algo mas bien simple.
    De ultima estoy seguro que puedo volver a hacerlo si es que queda mejor.
-}
whenM :: Bool -> MatchError -> Either MatchError a -> Either MatchError a
whenM True _ = id
whenM False er = const $ Left er

whenML :: Bool -> MatchError -> a -> Either MatchError a
whenML True _ = return
whenML False er = const $ Left er

-- | Aplica una substitución a una expresión dada.
applySubst :: PreExpr -> ExprSubst -> PreExpr
applySubst (Var v) s = M.findWithDefault (Var v) v s
applySubst (UnOp op e) s = UnOp op $ applySubst e s
applySubst (BinOp op e f) s = BinOp op (applySubst e s) (applySubst f s)
applySubst (App e f) s = App (applySubst e s) (applySubst f s)
applySubst (Quant q v e1 e2) s = Quant q v (applySubst e1 s) (applySubst e2 s)
applySubst (Paren e) s = Paren $ applySubst e s
applySubst (PrExHole h) _ = PrExHole h
applySubst (Con c) _ = Con c
applySubst (Fun f) _ = Fun f

{- Función que implementa el algoritmo de matching. Toma una lista de variables
que están ligadas a algún cuantificador, una expresión patrón, otra expresión y
un mapa de sustituciones. 
-}
match' :: [Variable] -> PreExpr -> PreExpr -> ExprSubst 
                                           -> Either MatchError ExprSubst
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
match' bvs e@(Var v) e' s | e == e' = return s -- Sería mas prolijo tener Right ?
                          | v `elem` bvs = Left $ BindingVar v
                          | otherwise = 
                              maybe (return $ M.insert v e' s) -- Sería mas prolijo tener Right ?
                                    (\f -> whenML (e' == f) (DoubleMatch v f e') s)
                                    $ M.lookup v s
-- En caso de error devuelvo InequNameFunc
match' bvs (UnOp op1 e1) (UnOp op2 e2) s = whenM (op1==op2) (InequOperator op1 op2) $
                                                            match' bvs e1 e2 s
-- En caso de error devuelvo InequNameFunc
match' bvs (BinOp op1 e1 e2) 
           (BinOp op2 f1 f2) s = whenM (op1==op2) (InequOperator op1 op2) $
                                                  match' bvs e1 f1 s >>= 
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
    whenM (q==p) (InequQuantifier q p) $ -- En caso de error devuelvo InequQuant
        if v==w then match' (v:bvs) e1 f1 s >>= match' (v:bvs) e2 f2
                else match' (fv:bvs) (subst v fv e1) (subst w fv f1) s >>=
                     match' (fv:bvs) (subst v fv e2) (subst w fv f2)
    where fv= freshVar $ S.unions [freeVars $ Var v,freeVars $ Var w,
                                   freeVars e1, freeVars e2,freeVars f1, 
                                   freeVars f2]
          subst = substitution
-- Caso particular de intentar matchear una variable con una función.
{-match' _ (Fun _) (Var _) s = Left FuncWithVar
-- Caso particular de intentar matchear una variable con una constante.
match' _ (Con _) (Var _) s = Left ConstWithVar
-- El nombre de las funciones debe ser el mismo.
match' _ (Fun f1) (Fun f2) s = whenML (f1==f2) InequNameFunc s
-- Para matchear constantes deben ser exactamente la misma.
match' _ (Con c1) (Con c2) s = whenML (c1==c2) InequNameConst s
-- Si no estamos en ningun caso anterior, entonces solo hay matching
-- si las expresiones son iguales.
-- En caso de error devuelvo InequPreExpr -}
match' _ e1 e2 s = whenML (e1==e2) (InequPreExpr e1 e2) s

{-| match toma una expresión patrón y otra que quiere matchearse con el patrón.
Si hay matching, retorna el mapa de sustituciones que deben realizarse
simultáneamente para llegar desde la expresión patrón a la expresión dada.
-}
match :: PreExpr -> PreExpr -> Either MatchError ExprSubst
match e e' = match' [] e e' M.empty
