{-# Language GADTs #-}

{-| Este m&#243;dulo define la noci&#243;n de una prueba. -}
module Equ.Proof (
                   encode, decode
                 , newProof, newProofWithoutEnd, addStep
                 , proofFromTruth, fillHole
                 , Truth (..)
                  -- * Axiomas y teoremas
                 , Axiom(..)
                 , Theorem(..)
                 -- * Pruebas
                 -- $proofs
                 , Proof(..)
                 , Basic(..)
                 -- * Ejemplos
                 -- $samples
                 , module Equ.Proof.Zipper
                 , module Equ.Proof.Monad
                 , module Equ.Proof.Error
                 , module Equ.Rewrite
                 ) where

import Equ.Proof.Proof hiding (getCtx,getStart,getEnd,getRel,setCtx)
import Equ.Proof.Zipper
import Equ.Proof.Monad
import Equ.Proof.Error

import Equ.PreExpr hiding (replace)
import Equ.Rule
import Equ.Rewrite

import Data.Monoid(mappend)
import Data.Either(partitionEithers)

import Data.Map (empty)
import Control.Monad

-- Funcion para checkear igualdad, con la variante importante que en caso de
-- no cumplirse devolvemos un resultado por default.
checkEqWithDefault :: Eq a => d -> a -> a -> Either d ()
checkEqWithDefault def a b | a /= b = Left def
                           | otherwise = Right ()

whenEqWithDefault :: Eq a => ProofError -> a -> a -> PM ()
whenEqWithDefault def a b = whenPM (==a) def b >> return ()

{- 
Funciones para construir y manipular pruebas.
Este kit de funciones debería proveer todas las herramientas
necesarias para desarrollar pruebas en equ 
-}

proofFromRule :: Truth t => Focus -> Focus -> Relation -> t -> (t -> Basic) -> 
                            Rule -> PM Proof
proofFromRule f1 f2 rel t mkBasic r = whenEqWithDefault err rel (truthRel t) >>
                                      liftRw (focusedRewrite f1 r) >>= \f ->
                                      whenEqWithDefault err f f2 >>
                                      return (Simple empty rel f1 f2 $ mkBasic t)
        where err :: ProofError
              err = BasicNotApplicable $ mkBasic t

-- | Dados dos focuses f1 y f2, una relacion rel y un axioma o
-- teorema, intenta crear una prueba para f1 rel f2, utilizando el
-- paso simple de aplicar el axioma o teorema.
proofFromTruth :: Truth t => Focus -> Focus -> Relation -> t -> PM Proof
proofFromTruth f f' r t = case partitionEithers $
                               map (proofFromRule f f' r t truthBasic) 
                                   (truthRules t)
                          of
                          -- Devolvemos el primer error, esto tal vez se
                          -- podría mejorar un poco devolviendo la lista de
                          -- errores.
                          (er:ers, []) -> Left er
                          (_, p:ps) -> Right p

-- | Igual que proofFromTruth, pero ahora cambiamos el contexto.
proofFromTruthWithCtx :: Truth t => Ctx -> Focus -> Focus -> Relation -> t 
                         -> PM Proof
proofFromTruthWithCtx c f f' r b = either Left
                                          (setCtx c)
                                          (proofFromTruth f f' r b)

proofFromAxiom :: Focus -> Focus -> Relation -> Axiom -> PM Proof
proofFromAxiom = proofFromTruth

proofFromTheorem :: Focus -> Focus -> Relation -> Theorem -> PM Proof
proofFromTheorem  = proofFromTruth

{- | Comenzamos una prueba dados dos focus y una relación entre ellas, de 
        la cual no tenemos una prueba.
    {POS: El contexto de la prueba es vacio.}
    Dadas rel, f y f' tenemos una prueba del estilo;
    
@
    f
rel {?}
    f'
@
-}
newProof :: Relation -> Focus -> Focus -> Proof
newProof = Hole empty

{- | Comenzamos una prueba dado unfocus y una relacion.
    {POS: El contexto de la prueba es vacio.}
    Dadas rel y f tenemos una prueba del estilo;
    
@
    f
rel {?}
    ?{}
@
-}
newProofWithoutEnd :: Relation -> Focus -> HoleInfo -> Proof
newProofWithoutEnd r f hi = Hole empty r f h
    where h = toFocus $ preExprHole hi

{- | Dado un proofFocus (p, path) y una prueba p', agregamos un paso.

p:

@
    startP
rel {?}
    endP
@

p':

@
    startP'
rel { b }
    endP'
@

    addStep (p, path) p' (sii startP == startP')
    
p'':

@
    startP
rel { b }
    endP'
rel {?}
    EndP
@

    addStep (p, path) p' (sii endP == startP')

p'':

@
    startP
rel {?}
    startP'
rel { b }
    endP'
@
-}
addStep :: ProofFocus -> Proof -> PM Proof
addStep (p@(Hole c r f f'), _) p' = do
                c' <- getCtx p'
                whenEqWithDefault (ClashCtx c c') c c'
                r' <- getRel p'
                whenEqWithDefault (ClashRel r r') r' r
                endP' <- getEnd p' -- Acá no recuerdo si ibamos a querer esto.
                when (isPreExprHole endP') (Left $ ProofEndWithHole p')
                case getStart p' of
                     Right cf | cf == f -> return $ p' `mappend` p'' 
                     Right cf | cf == f' -> return $ p `mappend` p' 
                     _ -> Left $ ClashAddStep p p'
    where
        Right endP' = getEnd p'
        p'' = newProof r endP' f'
addStep (p, _) _ = Left $ ClashProofNotHole p

-- | Completa un hueco en una prueba.
fillHole :: Truth t => ProofFocus -> t -> PM ProofFocus
fillHole pf@(Hole c r f f', _) t = either Left
                                          (Right . replace pf) $
                                          proofFromTruthWithCtx c f f' r t
fillHole (p, _) _ = Left $ ClashProofNotHole p
