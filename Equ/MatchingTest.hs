module Equ.MatchingTest where

import Equ.Expr
import Equ.Rule
import Equ.Types
import Equ.Parser
import Equ.Syntax
import Equ.Theories.FOL
import Equ.Theories.List
import Equ.PreExpr.Internal

import Data.Map as M
import Data.Text as T
import Data.List as L

-- Subtitucion.
type Sigma = M.Map Variable PreExpr

-- Función principal de matching.
matching :: PreExpr -> PreExpr -> Maybe Sigma
matching pe pe' = matchingPreExpr pe pe' M.empty

-- Matching para variables.
matchingVar :: Variable -> PreExpr -> Sigma -> Maybe Sigma
matchingVar v pe s = case M.lookup v s of
                    Nothing -> Just $ M.insert v pe s
                    Just x -> if x == pe 
                                 then Just s -- De acá para a bajo esta super parchado!
                                 else case x of
                                        Var x' -> if '0' `L.elem` show x'
                                                    then Just $ M.insert x' pe s
                                                    else Nothing
{-
Acá me encontre con un problema que no se me ocurrio como resolver
sin empezar a cambiar muchas cosas que tenia hechas. El problema es que
cuando renombro una variable porque esta libre, luego cuando prosigo
con el maching de la expresion me encuentro con la variable libre
que, apezar de tener anotado que hay que colocar una fresca, en su lugar
esta la variable libre (no fresca). Es decir, una manera sería reescribiendo
la expresion a medida que se hace matching, la otra es marcar que esa variable
libre tiene un "alias". 
Revise que habia hecho ema para ver si se habia encontrado con este problema,
pero creo que tiene el mismo problema.
Caso que me trae problemas => 
matching (parser "〈∀ x : x = z : F@x〉") (parser "〈∀ z : z = F@a : F@z〉")
-}

-- Matching para cuantificadores y sus variables.
matchingQuantAndVar :: Quantifier -> Quantifier -> 
                       Variable -> Variable -> 
                       PreExpr -> PreExpr ->
                       Sigma -> Maybe Sigma
matchingQuantAndVar q q' v v' pe pe' s = 
    matchingAux q q' s >>= 
    matchingVar v (Var v') >>=
    if v == v' || 
        (v' `L.notElem` freeVars pe &&
        v' `L.notElem` freeVars pe')
    then Just
    else searchFreshVar v' pe pe'

-- Auxiliar para calcular las variables libres de una preExpresion.
freeVars' :: [Variable] -> PreExpr -> [Variable]
freeVars' lv (Var v) = v : lv
freeVars' lv (Con _) = lv
freeVars' lv (Fun _) = lv
freeVars' lv (PrExHole _) = lv
freeVars' lv (UnOp _ pe) = freeVars' lv pe
freeVars' lv (BinOp _ pe pe') = freeVars' lv pe ++ freeVars' lv pe'
freeVars' lv (App pe pe') = freeVars' lv pe ++ freeVars' lv pe'
freeVars' lv (Paren pe) = freeVars' lv pe
freeVars' lv (Quant _ v pe pe') = L.delete v $ freeVars' lv pe ++ freeVars' lv pe'

-- Dada una preExpresion devuelve una lista con las variables libres.
freeVars :: PreExpr -> [Variable]
freeVars = freeVars' []

-- Busca una variable fresca para usar. Asume que la variable
-- que se le pasa por argumento no es fresca.
searchFreshVar :: Variable -> PreExpr -> PreExpr -> Sigma -> Maybe Sigma
searchFreshVar = searchFreshVar' 0

-- Auxiliar para calcular searchFreshVar
searchFreshVar' :: Int -> Variable -> PreExpr -> PreExpr -> Sigma -> Maybe Sigma
searchFreshVar' n v pe pe' s = let name = (T.unpack . tRepr) v ++ show n
                                   w = var name (varTy v)
                               in if w `L.notElem` freeVars pe
                                  then Just $ M.insert v (Var w) s
                                  else searchFreshVar' (n+1) v pe pe' s

-- Auxiliar para decidir si existe matching entre 
-- nombres de constantes, funciones... 
matchingAux :: (Eq a) => a -> a -> Sigma -> Maybe Sigma
matchingAux e e' s = if e == e' then Just s else Nothing

-- Matching para preExpresiones.
-- Algo interesante a comentar es que en principio me parecio no tener
-- problemas con los cuantificadores, la realidad es que no creo que haya
-- salvo que cuando quiero reescribir el termino en base al sigma devuelto
-- por el matching tengo varios problemas. Es por esto que hay que introducir
-- alguna que otra manera de diferenciar esto y insertar variables frescas.
matchingPreExpr :: PreExpr -> PreExpr -> Sigma -> Maybe Sigma
matchingPreExpr (Var v) pe s = matchingVar v pe s
matchingPreExpr (Con c) (Con c') s = matchingAux c c' s
matchingPreExpr (Fun f) (Fun f') s = matchingAux f f' s
matchingPreExpr (PrExHole h) (PrExHole h') s = Just s
matchingPreExpr (UnOp op pe) (UnOp op' pe') s =  
    matchingAux op op' s >>=
    matchingPreExpr pe pe'
matchingPreExpr (BinOp op pe pe') (BinOp op' pe'' pe''') s = 
    matchingAux op op' s >>=
    matchingPreExpr pe pe'' >>=
    matchingPreExpr pe' pe'''
matchingPreExpr (App pe pe') (App pe'' pe''') s = 
    matchingPreExpr pe pe'' s >>=
    matchingPreExpr pe' pe'''
matchingPreExpr (Quant q v pe pe') (Quant q' v' pe'' pe''') s =
    matchingQuantAndVar q q' v v' pe pe' s >>=
    matchingPreExpr pe pe'' >>=
    matchingPreExpr pe' pe'''
matchingPreExpr (Paren pe) (Paren pe') s = matchingPreExpr pe pe' s
matchingPreExpr (Paren pe) pe' s = matchingPreExpr pe pe' s
matchingPreExpr pe (Paren pe') s = matchingPreExpr pe pe' s
matchingPreExpr _ _ _ = Nothing

-- De acá en adelante es un intento de implementación del algoritmo que
-- discutimos con miguel y ema sobre reescritura. La idea estructural la saque
-- de lo que implemento ema.

rewrite :: Expr -> Rule -> Maybe PreExpr
rewrite (Expr pe) r = let (Expr lhsr) = lhs r
                          (Expr rhsr) = rhs r
                        in
                        matching lhsr pe >>= Just . (flip subsumes) rhsr 

-- Reescritura de dos preExpresiones.
rewrite2 :: PreExpr -> PreExpr -> Maybe PreExpr
rewrite2 pe pe' = matching pe pe' >>= Just . (flip subsumes) pe'

subsumes :: Sigma -> PreExpr -> PreExpr
subsumes s = (>>= flip findVar s)

findVar :: Variable -> Sigma -> PreExpr
findVar v = M.findWithDefault (Var v) v
