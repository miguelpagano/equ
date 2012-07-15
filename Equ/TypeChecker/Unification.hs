-- | Transforma una PreExpresi&#243;n en una Expresi&#243;n.
module Equ.TypeChecker.Unification
    ( module Equ.TypeChecker.Error      
      -- * Algoritmo de unificaci&#243;n con relaci&#243;n de orden.
    , unify
    , emptySubst
    , unifyList
    , unifyTest
    , unificate
    , rewrite
    , findVar
    , match
    , TySubst
    )
    where


import Equ.Types
import Equ.TypeChecker.Error

import qualified Data.Map as M
-- TODO: tener en cuenta subtipado
-- import Data.Poset (leq) 

-- | Tipo de la sustituci&#243;n para unificar expresiones de tipo.
type TySubst = M.Map TyVarName Type

-- | Aplicar una sustituci&#243;n (finita) a un variable de tipo.
findVar :: TyVarName -> TySubst -> Type
findVar v = M.findWithDefault (TyVar v) v

-- | Uso de una sustituci&#243;n para reemplazar todas las variables en un
-- tipo.
rewrite :: TySubst -> Type -> Type
rewrite s = (>>= (\v -> findVar v s))


-- | Algoritmo de unificaci&#243;n. Suponemos que no hay 'TyUnknown'.
unify :: Type -> Type -> TySubst -> Either TyErr TySubst
unify t@(TyAtom _) t'@(TyAtom _) s | t == t' = return s
                                   | otherwise = Left $ ErrUnification t t' (M.toList s)
unify (t :-> t') (r :-> r') s = unify t r s >>= unify t' r'
unify (TyList t) (TyList t') s = unify t t' s
unify t@(TyVar v) t' s | t == t' = return s
                       | v `occurs` t' = Left $ ErrUnification (TyVar v) t' (M.toList s)
                       | v `M.member` s  = unify (M.findWithDefault TyUnknown v s) t' s
                       | otherwise = return . M.insert v t' . M.map ((tyreplace v) t') $ s
unify t (TyVar v) s = unify (TyVar v) t s
unify t t' s = Left $ ErrUnification t t' (M.toList s)

unifyList :: [Type] -> TySubst -> Either TyErr TySubst
unifyList [] s = return s
unifyList [t] s = return s
unifyList (t:t':ts) s = unify t t' s >>= unifyList ts

-- | Usamos unify para comprobar si existe o no unificaci&#243;n. 
--   Suponemos que no hay 'TyUnknown'.
unifyTest :: Type -> Type -> Bool
unifyTest t t' = either (const False) (const True) $ unify t t' emptySubst

-- | Sustituci&#243;n vac&#237;a.
emptySubst :: TySubst
emptySubst = M.empty

unificate :: Type -> Type -> Maybe Type
unificate t t' = either (const Nothing) (return . flip rewrite t) $ unify t t' emptySubst

-- | Devuelve True si el tipo izquierdo matchea con el derecho.
match :: Type -> Type -> Bool
match (TyVar v) w = True
match (TyList t) (TyList t') = match t t'
match (t1 :-> t2) (t1' :-> t2') = match t1 t1' && match t2 t2'
match t t' = t == t'
