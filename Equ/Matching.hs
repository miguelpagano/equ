module Equ.Matching
    ( module Equ.Matching.Error
    , match
    , applySubst
    , ExprSubst
    , MatchMErr
    , matcherr
    )
    where

import Equ.Matching.Error
import Equ.PreExpr

import qualified Data.Map as M
import qualified Data.Set as S

import Control.Monad.RWS (runRWS)
import Control.Monad.Trans.Either (runEitherT, hoistEither)
import Control.Monad.RWS.Class(ask)

-- | Mapa de substituciones de variable - preExpresiones.
type ExprSubst = M.Map Variable PreExpr

-- | Estructura general para los errores informativos con contexto.
type MatchMErr = (Focus,MatchError)

-- | Mónada de estado para matching.
type MatchState = MonadTraversal MatchMErr ExprSubst

-- | Generación de mensaje de Error.
matcherr :: MatchError -> MatchState a
matcherr err = ask >>= \foc -> hoistEither $ Left (foc, err)

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
    VERSIÓN 2; Tanto para whenM2 como para whenML2 cambio los tipos y
    tenemos el caso especial de usar el generador de errores en caso de
    error.
-}
whenM :: Bool -> MatchError -> MatchState ExprSubst -> MatchState ExprSubst
whenM True _ = id
whenM False er = const $ matcherr er

whenML :: Bool -> MatchError -> ExprSubst -> MatchState ExprSubst
whenML True _ = return
whenML False er = const $ matcherr er

{- Función que implementa el algoritmo de matching. Toma una lista de variables
que están ligadas a algún cuantificador, una expresión patrón, otra expresión y
un mapa de sustituciones. 
-}
match' :: [Variable] -> PreExpr -> PreExpr -> ExprSubst -> MatchState ExprSubst
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
                           | v `elem` bvs = matcherr $ BindingVar v
                           | otherwise = 
                              maybe (return $ M.insert v e' s)
                                    (\f -> whenML (e' == f) (DoubleMatch v f e') s)
                                    $ M.lookup v s

match' bvs (UnOp op1 e1) (UnOp op2 e2) s = whenM (op1==op2) 
                                            (InequOperator op1 op2) $ 
                                            localGo goDown (match' bvs e1 e2 s)


{-
    VERSIÓN 2; Para operadores iguales, cada vez que pretendo intentar matchear
    las expresiones internas, cambio el enviroment segun corresponda.
-}
match' bvs (BinOp op1 e1 e2) (BinOp op2 f1 f2) s = 
                    whenM (op1==op2) (InequOperator op1 op2) $
                                    (localGo goDown $ match' bvs e1 f1 s) >>= 
                                    ((localGo goDownR) . match' bvs e2 f2)

match' bvs (App e1 e2) (App f1 f2) s = (localGo goDown $ match' bvs e1 f1 s) >>= 
                                       ((localGo goDownR) . match' bvs e2 f2)

{-
    VERSIÓN 2; Un detalle no menor acá es que como navegamos solamente
    por el focus de la expresión a matchear, es decir no la expresión patron,
    en el primer caso de los parentesis no cambiamos el enviroment.
-}
match' bvs (Paren e1) e2 s = match' bvs e1 e2 s
match' bvs e1 (Paren e2) s = localGo goDown $ match' bvs e1 e2 s

{-
Para matchear dos expresiones cuantificadas, deben ser el mismo cuantificador.
Si las variables cuantificadas v y w son la misma, entonces hacemos matching en 
las subexpresiones, agregando v a la lista de variables ligadas bvs.
Si v/=w, entonces reemplazamos v y w por una variable fresca en ambas expresiones
y luego realizamos matching en las subexpresiones, agregando la variable fresca
a bvs.

VERSIÓN 2; Cada vez que voy a intentar matchear las expresiones internas del
    cuantificador, cambio el enviroment, es decir, navego el focus con la
    dirección que corresponda. Para esto uso dos funciones localGoL y localGoR
    que representan navegar por izquierda o por derecha respectivamente.
-}    

match' bvs (Quant q v e1 e2) (Quant p w f1 f2) s =
    whenM (q==p) (InequQuantifier q p) $ -- En caso de error devuelvo InequQuant
        if v==w then (localGo goDown $ match' (v:bvs) e1 f1 s) >>= (localGo goDownR) . match' (v:bvs) e2 f2
                else (localGo goDown $ match' (fv:bvs) (subst v fv e1) (subst w fv f1) s) >>=
                     (localGo goDownR) . match' (fv:bvs) (subst v fv e2) (subst w fv f2)
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
-- En caso de error devuelvo InequPreExpr 

    VERSIÓN 2; Ninguna diferencia con el original.
   -}
match' _ e1 e2 s = whenML (e1==e2) (InequPreExpr e1 e2) s

{- | VERSIÓN 2; Función principal de matching.
    
    Primer intento de agregar información al intentar realizar matching.
    Hasta el momento se podría decir que tenemos dos grandes novedades con
    respecto a la función vieja. Disponemos de un log y hacemos uso de focus
    para rastrear donde estamos en la expresión que intentamos matchear.
    Sobre el log todavía no hago ninguna utilización, estaría bueno usarlo
    para llevar la cuenta de que matching he podido realizar?.
    Sobre el focus, la idea es recorrer la expresión que estamos intentando
    matchear, esta aclaración es importante ya que está la otra opción de 
    recorrer la expresión patrón.
    
    Cosas interesantes; me base fuertemente en el modulo TypeChecker. Tan así
    que la función principal basicamente la copie y pegue de la función que 
    hizo miguel, creditos a él :). 
    Yo no termino de entender bien como es que operta.
    
    Algunas aclaraciones a parte; no quise borrar lo hecho por las dudas y de 
    ahí que tenemos esta versión 2.

-}
{-| match toma una expresión patrón y otra que quiere matchearse con el patrón.
Si hay matching, retorna el mapa de sustituciones que deben realizarse
simultáneamente para llegar desde la expresión patrón a la expresión dada.
-}
match :: PreExpr -> PreExpr -> Either (MatchMErr,Log) ExprSubst
match e e' = case runRWS (runEitherT (match' [] e e' M.empty)) (toFocus e') M.empty of
                   (res, _, l) -> either (\err -> Left (err,l)) (Right) res
