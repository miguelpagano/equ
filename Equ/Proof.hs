{-# Language GADTs #-}

{-| Este m&#243;dulo define la noci&#243;n de una prueba. -}
module Equ.Proof (newProof, newProofWithoutEnd, addStep
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

import qualified Equ.PreExpr as PE hiding (replace)
import Equ.Rule
import Equ.Rewrite

import Data.Monoid(mappend)
import Data.Either(partitionEithers)

import Data.Map (empty, singleton)
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
Este kit de funciones deber&#237;a proveer todas las herramientas
necesarias para desarrollar pruebas en equ.
-}

proofFromRule :: Truth t => PE.Focus -> PE.Focus -> Relation -> t -> (t -> Basic) -> 
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
proofFromTruth :: Truth t => PE.Focus -> PE.Focus -> Relation -> t -> PM Proof
proofFromTruth f f' r t = case partitionEithers $
                               map (proofFromRule f f' r t truthBasic) 
                                   (truthRules t)
                          of
                          -- Devolvemos el primer error, esto tal vez se
                          -- podr&#237;a mejorar un poco devolviendo la lista de
                          -- errores.
                          ([],[]) -> Left undefined -- TODO: FIX THIS CASE!
                          ([er], []) -> Left er
                          (_, p:ps) -> Right p

-- | Igual que proofFromTruth, pero ahora cambiamos el contexto.
proofFromTruthWithCtx :: Truth t => Ctx -> PE.Focus -> PE.Focus -> Relation -> t
                         -> PM Proof
proofFromTruthWithCtx c f f' r b = either Left
                                          (setCtx c)
                                          (proofFromTruth f f' r b)

{- | Comenzamos una prueba dados dos focus y una relaci&#243;n entre ellas, de 
        la cual no tenemos una prueba.
    {POS: El contexto de la prueba es vacio.}
    Dadas rel, f y f' tenemos una prueba del estilo;
    
@
    f
rel {?}
    f'
@
-}
newProof :: Relation -> PE.Focus -> PE.Focus -> Proof
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
newProofWithoutEnd :: Relation -> PE.Focus -> PE.HoleInfo -> Proof
newProofWithoutEnd r f hi = Hole empty r f h
    where h = PE.toFocus $ PE.preExprHole hi

{- | Comenzamos una prueba con el meta-teorema de deducción.
Dadas hip y f generamos una prueba del estilo;

@
    hip
⇒   {?}
    f
@
Donde en el contexto de la prueba tenemos a hip.

-}
newProofWithHip :: PE.Focus -> PE.Focus -> Proof
newProofWithHip hip@(e,_) f = Deduc ctx hip f $ Hole ctx relImpl hip f
    where ctx :: Ctx
          ctx = beginCtx e

{- | Comenzamos una prueba por casos. -}

newProofWithCases :: Relation -> PE.Focus -> PE.Focus -> PE.Focus -> [PE.Focus] -> Proof
newProofWithCases r f f' c lc = Cases ctx r f f' c lp
    where ctx :: Ctx
          ctx = ctxFromList lc
          lp :: [(PE.Focus, Proof)]
          lp = map (\fi@(ei,_) -> (fi, Hole (beginCtx ei) r f f')) lc

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
                endP' <- getEnd p' -- Ac&#225; no recuerdo si ibamos a querer esto.
                when (PE.isPreExprHole endP') (Left $ [ProofEndWithHole p'])
                case getStart p' of
                     Right cf | cf == f -> return $ p' `mappend` p'' 
                     Right cf | cf == f' -> return $ p `mappend` p' 
                     _ -> Left $ [ClashAddStep p p']
    where
        Right endP' = getEnd p'
        p'' = newProof r endP' f'
addStep (p, _) _ = Left $ [ClashProofNotHole p]

-- | Completa un hueco en una prueba.
fillHole :: Truth t => ProofFocus -> t -> PM ProofFocus
fillHole pf@(Hole c r f f', _) t = either Left
                                          (Right . replace pf) $
                                          proofFromTruthWithCtx c f f' r t
fillHole (p, _) _ = Left $ [ClashProofNotHole p]

{-
5. Definir funciones que comprueban que un elemento de tipo Proof
es realmente una prueba.

Entiendo que algo de tipo Proof sera una prueba cuando se cumpla lo 
siguiente; Sea P de tipo Proof
* P no es Hole, al igual que ninguna de sus ramas.
* Todas las expresiones de la prueba estan bien tipadas. Acá la duda es,
 deberíamos hacer checkPreExpr de cada expresión que se encuentre en la 
 prueba y ver que todas las expresiones sean "tipables" (?) 
 O hay que hacer un poquito mas y lo que deberíamos hacer es, ademas de
 hacer checkPreExpr como antes, ver que el conjunto de tipos que nos quedo
 sean unificables de a pares (?)

Como PRE importante considero que cada vez que se agregaba un paso en una 
en un prueba se comprobaba que las expresiones "matchearan" como
correspondían y ademas que al ingresar un axioma o teorema este se aplico 
correctamente.
-}

isCompleteProof :: Proof -> Either ProofFocus Bool
isCompleteProof = isCompleteProofFocus . toProofFocus

isCompleteProofFocus :: ProofFocus -> Either ProofFocus Bool
isCompleteProofFocus p = 
            case (goDownL p, goDownR p) of
                ((Just plf@(Hole _ _ _ _, _)), _) -> Left plf
                (_,(Just prf@(Hole _ _ _ _, _))) -> Left prf
                (Just lp, Just rp) -> isCompleteProofFocus lp >> 
                                      isCompleteProofFocus rp
                (Just lp, Nothing) -> isCompleteProofFocus lp >> 
                                      return True
                (Nothing, _) -> case p of
                                     (Hole _ _ _ _, _) -> Left p
                                     _ -> return True
