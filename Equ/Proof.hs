{-# Language GADTs #-}
{-| En este módulo se definen las maneras posibles de construir
pruebas y las maneras básicas (axiomas, teoremas ya probados o
hipotesis) en que se puede justificar un paso lógico. Notar que la
verificación de que un paso de prueba está justificado depende en
ultima instancia del algoritmo de matching (y eventualmente la
normalizacion de expresiones que debe ser entendida como la generacion
automática de pasos inmediatos utilizando las reglas de reescritura).
-}
module Equ.Proof (
                   encode, decode
                 , newProof, newProofWithoutEnd, addStep
                 , proofFromTruth, fillHole
                 , holeProof, emptyProof, updateStart, updateEnd, updateRel
                 , validateProof, toHoleProof
                 , simpleProof, addEmptyStep, updateStartFocus, updateEndFocus
                 , updateMiddleFocus
                 , Truth (..)
                 , Axiom(..)
                 , Theorem(..)
                 , Proof(..)
                 , Basic(..)
                 --, Basic(..)
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

import Data.Map (empty, singleton)
import Data.Maybe
import Control.Monad

-- Funcion para checkear igualdad, con la variante importante que en caso de
-- no cumplirse devolvemos un resultado por default.
checkEqWithDefault :: Eq a => d -> a -> a -> Either d ()
checkEqWithDefault def a b | a /= b = Left def
                           | otherwise = Right ()

whenEqWithDefault :: Eq a => ProofError -> a -> a -> PM ()
whenEqWithDefault def a b = whenPM (==a) def b >> return ()

checkSimpleStepFromRule :: Truth t => Focus -> Focus -> Relation -> t -> Rule
                              -> PM ()
checkSimpleStepFromRule f1 f2 rel t rule = 
    whenEqWithDefault errRel rel (truthRel t) >>
    liftRw (focusedRewrite f1 rule) >>= \f ->
    whenEqWithDefault err f f2 
    
    where errRel :: ProofError
          errRel = ClashRel rel (truthRel t)
          err :: ProofError
          err = BasicNotApplicable $ truthBasic t

{- 
Funciones para construir y manipular pruebas.
Este kit de funciones deber&#237;a proveer todas las herramientas
necesarias para desarrollar pruebas en equ.
-}

proofFromRule :: Truth t => Focus -> Focus -> Relation -> t -> 
                            Rule -> PM Proof
proofFromRule f1 f2 rel t r = checkSimpleStepFromRule f1 f2 rel t r >>
                                      (return $ Simple empty rel f1 f2 $ truthBasic t)


-- | Dados dos focuses f1 y f2, una relacion rel y un axioma o
-- teorema, intenta crear una prueba para f1 rel f2, utilizando el
-- paso simple de aplicar el axioma o teorema.
proofFromTruth :: Truth t => Focus -> Focus -> Relation -> t -> PM Proof
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
proofFromTruthWithCtx :: Truth t => Ctx -> Focus -> Focus -> Relation -> t
                         -> PM Proof
proofFromTruthWithCtx c f f' r b = either Left
                                          (setCtx c)
                                          (proofFromTruth f f' r b)

{- | Comenzamos una prueba dados dos focus y una relaci&#243;n entre ellas, de 
=======
proofFromTruth f1 f2 rel t = firstRight err $
                             map (proofFromRule f1 f2 rel t) (truthRules t)
    where err :: PM Proof
          err = Left $ BasicNotApplicable $ truthBasic t


notValidSimpleProof :: Truth t => Focus -> Focus -> Relation -> t -> Proof
notValidSimpleProof f1 f2 r t = Simple empty r f1 f2 $ truthBasic t
          
proofFromAxiom :: Focus -> Focus -> Relation -> Axiom -> PM Proof
proofFromAxiom = proofFromTruth

proofFromTheorem :: Focus -> Focus -> Relation -> Theorem -> PM Proof
proofFromTheorem  = proofFromTruth

validateProof :: Proof -> PM Proof
validateProof (Hole ctx rel f1 f2) = Left ProofError
validateProof proof@(Simple ctx rel f1 f2 b) = 
    proofFromTruth f1 f2 rel b >>
    return proof
validateProof proof@(Trans ctx rel f1 f2 f p1 p2) = 
    getStart p1 >>= whenEqWithDefault err f1 >>
    getEnd p1 >>= whenEqWithDefault err f >>
    getStart p2 >>= whenEqWithDefault err f >>
    getEnd p2 >>= whenEqWithDefault err f2 >>
    validateProof p1 >> validateProof p2 >>
    return proof
    
    where err :: ProofError
          err = TransInconsistent proof
    
validateProof _ = undefined




{- | Comenzamos una prueba dados dos focus y una relación entre ellas, de 
>>>>>>> 60ec238656607b7f4d5e160d72b7aad8c2fe7b3f
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
holeProof :: Relation -> Proof
holeProof r = newProof r emptyExpr emptyExpr

-- | ProofFocus vacio
emptyProof :: Relation -> ProofFocus
emptyProof r = toProofFocus $ holeProof r




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

{- | Comenzamos una prueba con el meta-teorema de deducción.
Dadas hip y f generamos una prueba del estilo;

@
    hip
⇒   {?}
    f
@
Donde en el contexto de la prueba tenemos a hip.

-}
newProofWithHip :: Focus -> Focus -> Proof
newProofWithHip hip@(e,_) f = Deduc ctx hip f $ Hole ctx relImpl hip f
    where ctx :: Ctx
          ctx = beginCtx e

{- | Comenzamos una prueba por casos. -}

newProofWithCases :: Relation -> Focus -> Focus -> Focus -> [Focus] -> Proof
newProofWithCases r f f' c lc = Cases ctx r f f' c lp
    where ctx :: Ctx
          ctx = ctxFromList lc
          lp :: [(Focus, Proof)]
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
                when (isPreExprHole endP') (Left $ [ProofEndWithHole p'])
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

-- | Función para convertir una prueba Simple en un Hole
toHoleProof :: ProofFocus -> ProofFocus
toHoleProof (p@(Simple ctx r f f' b),path) = (Hole ctx r f f',path)
toHoleProof pf = pf

{- Funciones para pasar de una prueba vacía a una prueba con más contenido.
   Todas las funciones no validan la prueba, son solo para manipulacion -}

{- | Convierte una prueba vacía en un Simple o transforma una prueba simple en otra.
     Si la prueba no es vacía o no es simple, entonces se comporta como la identidad
     -}
simpleProof :: ProofFocus -> Basic -> ProofFocus
simpleProof (p@(Hole ctx r f1 f2),path) b =
    (Simple ctx r f1 f2 b,path)
simpleProof (p@(Simple ctx r f1 f2 b'),path) b =
    (Simple ctx r f1 f2 b,path)
simpleProof p _ = p



{- | Pasa de una prueba vacia a una prueba transitiva vacia. Si la prueba no es vacía
     o no es Simple, entonces se comporta como la identidad
     -}
addEmptyStep :: ProofFocus -> ProofFocus
addEmptyStep (p@(Hole ctx r f1 f2),path) = 
    (Trans ctx r f1 f2 emptyExpr (Hole ctx r f1 emptyExpr) (Hole ctx r emptyExpr f2),path)
-- Si le pasamos una prueba simple, la considera un hueco
addEmptyStep (p@(Simple ctx r f1 f2 b),path) = 
    (Trans ctx r f1 f2 emptyExpr (Hole ctx r f1 emptyExpr) (Hole ctx r emptyExpr f2),path)
addEmptyStep p = p




updateStartFocus :: ProofFocus -> Focus -> Maybe ProofFocus
updateStartFocus (p,path) f = Just (updateStart p f,path)

updateEndFocus :: ProofFocus -> Focus -> Maybe ProofFocus
updateEndFocus (p,path) f = Just (updateEnd p f,path)

updateMiddleFocus :: ProofFocus -> Focus -> Maybe ProofFocus
updateMiddleFocus (p,path) f = Just (updateMiddle p f,path)

