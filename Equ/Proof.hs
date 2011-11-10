{-# Language GADTs #-}

{-| Este m&#243;dulo define la noci&#243;n de una prueba. -}
module Equ.Proof (
                   encode, decode
                 , newProof, newProofWithoutEnd, addStep
                 , proofFromTruth, fillHole
                 , emptyProof, updateStart, updateEnd
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

import Equ.Proof.Proof hiding (getCtx,getStart,getEnd,getRel)
import Equ.Proof.Zipper
import Equ.Proof.Monad
import Equ.Proof.Error

import Equ.PreExpr hiding (replace)
import Equ.Rule
import Equ.Rewrite

import Data.Monoid(mappend)

import Data.Map (empty)
import Control.Monad

-- | Funciones auxiliares que podrían ir a su propio módulo.
isRight :: Either a b -> Bool
isRight (Right _) = True
isRight _ = False

firstWithDef :: a -> (a -> Bool) -> [a] -> a
firstWithDef def f xs = head $ filter f xs ++ [def]

firstRight :: Either a b -> [Either a b] -> Either a b
firstRight def = firstWithDef def isRight
                 

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
                                      (return $ Simple empty rel f1 f2 $ mkBasic t)
        where err :: ProofError
              err = BasicNotApplicable $ mkBasic t

-- | Dados dos focuses f1 y f2, una relacion rel y un axioma o
-- teorema, intenta crear una prueba para f1 rel f2, utilizando el
-- paso simple de aplicar el axioma o teorema.
proofFromTruth :: Truth t => Focus -> Focus -> Relation -> t -> PM Proof
proofFromTruth f1 f2 rel t = firstRight err $
                             map (proofFromRule f1 f2 rel t truthBasic) (truthRules t)
    where err :: PM Proof
          err = Left $ BasicNotApplicable $ truthBasic t


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
newProof r f f' = Hole empty r f f'

{- | Comenzamos una prueba dada una relación. No tenemos ni las expresiones
     ni la prueba.
    {POS: El contexto de la prueba es vacio.}
    Dada rel tenemos una prueba del estilo;
    
@
    Hole
rel {?}
    Hole
@
-}
emptyProof :: Relation -> Proof
emptyProof r = newProof r emptyExpr emptyExpr

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
addStep (p@(Hole ctx r f f'), _) p' = do
                ctx' <- getCtx p'
                whenEqWithDefault (ClashCtx ctx ctx') ctx ctx'
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
fillHole pf@(Hole ctx r f f', _) t = either (\er -> Left er)
                                            (\p -> Right $ replace pf p) $
                                            proofFromTruth f f' r t
fillHole (p, _) _ = Left $ ClashProofNotHole p
