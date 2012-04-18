{-# Language GADTs,OverloadedStrings #-}

{-| Este m&#243;dulo define la noci&#243;n de una prueba. -}
module Equ.Proof (newProof
                 , newProofWithStart 
                 , newProofWithoutEnd
                 , proofFromTruth
                 , holeProof, emptyProof, updateStart, updateEnd, updateRel, updateBasic
                 , validateProof, toHoleProof, validateProofFocus, validateListedProof
                 , validateStepProof
                 , simpleProof, addEmptyStep
                 , possibleExpr
                 , Truth (..)
                  -- * Axiomas y teoremas
                 , Axiom(..)
                 , Theorem(..)
                 , Basic(..)
                 , Hypothesis
                 -- * Pruebas
                 -- $proofs
                 , Proof(..)
                 , Proof'(..)
                 , ProofFocusAnnots(..)
                 , ProofAnnotation(..)
                 , emptyProofAnnots
                 , addEmptyStepAnnots
                 --, Basic(..)
                 -- * Ejemplos
                 -- $samples
                 , module Equ.Proof.Zipper
                 , module Equ.Proof.Monad
                 , module Equ.Proof.Error
                 , module Equ.Rewrite
                 , module Equ.Proof.ListedProof
                 -- * Funciones auxiliares
                 , addHypothesis
                 , getHypothesis
                 , addBoolHypothesis
                 , Name
                 , Ctx
                 ) where

import Equ.Proof.Annot
import Equ.Proof.Proof hiding (getCtx,getStart,getEnd,getRel,setCtx)
import qualified Equ.Proof.Proof as P(getStart,getEnd,getBasic)
import Equ.Proof.Zipper
import Equ.Proof.Monad
import Equ.Proof.Error
import Equ.Proof.ListedProof
import Equ.Theories.Common

import qualified Equ.PreExpr as PE hiding (replace)
import Equ.Expr
import Equ.PreExpr.Eval (evalExpr)
import Equ.Rule
import Equ.Rewrite

import Data.Monoid(mappend)

import Data.Maybe
import Data.Either (partitionEithers,rights)

import Control.Monad
import Control.Arrow

-- | Funciones auxiliares que podrían ir a su propio módulo.
isRight :: Either a b -> Bool
isRight (Right _) = True
isRight _ = False

firstWithDef :: a -> (a -> Bool) -> [a] -> a
firstWithDef def f xs = head $ filter f xs ++ [def]

firstRight :: Either a b -> [Either a b] -> Either a b
firstRight def = firstWithDef def isRight
                 

-- | Determina si dos expresiones son iguales al evaluar
-- todas las expresiones aritméticas.
checkEval :: PE.Focus -> PE.Focus -> Bool
checkEval e e' = evalExpr (PE.toExpr e) == evalExpr (PE.toExpr e')


-- Funcion para checkear igualdad, con la variante importante que en caso de
-- no cumplirse devolvemos un resultado por default.
checkEqWithDefault :: Eq a => d -> a -> a -> Either d ()
checkEqWithDefault def a b | a /= b = Left def
                           | otherwise = Right ()

whenEqWithDefault :: Eq a => ProofError -> a -> a -> PM a
whenEqWithDefault def a b = whenPM (==a) def b >> return b

whenEqWithDefault' :: Eq a => ProofError -> a -> (b -> a) -> b -> PM b
whenEqWithDefault' def a f b = whenPM (==a) def (f b) >> return b

notValidSimpleProof :: Truth t => PE.Focus -> PE.Focus -> Relation -> t -> Proof
notValidSimpleProof f1 f2 r t = Simple beginCtx r f1 f2 $ truthBasic t

whenEqRelWithDefault :: Eq a => ProofError -> a -> a -> [a] -> PM ()
whenEqRelWithDefault def a b rs = whenPM (\b -> b==a || b `elem` rs) def b >> 
                                  return ()

-- | Comprueba que el uso de una regla sea correcto. La relación que se
-- pasa como argumento es el de la prueba.
checkSimpleStepFromRule :: Truth t => PE.Focus -> PE.Focus -> Relation -> t -> 
                           Rule -> (ProofFocus -> ProofFocus) -> PM PE.Focus
checkSimpleStepFromRule f1 f2 rel t rule fMove = 
    whenEqRelWithDefault errRel rel (truthRel t) [relEquiv,relEq]>>
    case partitionEithers $ rewriteAllFocuses (PE.toExpr f1) rule of
         (_,[]) -> Left err
         (_,ls) -> case partitionEithers $ map checkeq ls of
                        (errors,[]) -> Left $ head errors
                        (_,xs) -> return . snd $ head xs
    where 
        errRel :: ProofError
        errRel = ProofError (ClashRel rel (truthRel t)) fMove
        err :: ProofError
        err = ProofError (BasicNotApplicable $ truthBasic t) fMove
        checkeq :: (PE.Focus,PE.Focus) -> PM (PE.Focus,PE.Focus)
        checkeq = whenEqWithDefault' err (PE.goTop f2) fst . (PE.goTop *** id)
{- 
Funciones para construir y manipular pruebas.
Este kit de funciones deber&#237;a proveer todas las herramientas
necesarias para desarrollar pruebas en equ.
-}
proofFromRule :: Truth t => PE.Focus -> PE.Focus -> Relation -> t -> 
                            Rule -> (ProofFocus -> ProofFocus) -> PM Proof
proofFromRule f1 f2 rel t r fMove = 
                        checkSimpleStepFromRule f1 f2 rel t r fMove >>= 
                        \f -> return $ Simple beginCtx rel f f2 $ truthBasic t
                                    
-- | Dados dos focuses f1 y f2, una relacion rel y un axioma o
-- teorema, intenta crear una prueba para f1 rel f2, utilizando el
-- paso simple de aplicar el axioma o teorema.
proofFromTruth :: PE.Focus -> PE.Focus -> Relation -> Basic -> 
                  (ProofFocus -> ProofFocus) -> PM Proof
proofFromTruth f f' r basic fMove = 
    case basic of
        Evaluate -> 
                if checkEval f f' 
                then Right $ Simple beginCtx r f f' Evaluate
                else Left $ ProofError (BasicNotApplicable Evaluate) fMove
        _ -> case partitionEithers $ 
                map (flip simples fMove) (truthRules basic) of
                    ([],[]) -> Left undefined -- TODO: FIX THIS CASE!
                    (_, p:ps) -> Right p
                    (er, []) -> Left $ head er
    where simples = proofFromRule f f' r basic

validateProofFocus :: ProofFocus -> PM Proof
validateProofFocus (pr,path) = validateProof pr

-- | Valida una prueba completa vista como lista
validateListedProof :: ListedProof -> PM Proof
validateListedProof lProof = validateProof (toProof $ pFocus lProof)

-- | Valida el paso de una prueba vista como lista.
validateStepProof :: ListedProof -> PM Proof
validateStepProof lProof = let p = (pList lProof)!!(selIndex lProof) in
                               validateProof p
                          
validateProof :: Proof -> PM Proof
validateProof p = validateProof' p goTop'
                          
validateProof' :: Proof -> (ProofFocus -> ProofFocus) -> PM Proof
validateProof' (Hole ctx rel f1 f2) moveFocus = Left $ ProofError HoleProof moveFocus
validateProof' proof@(Simple ctx rel f1 f2 b) moveFocus = 
    proofFromTruth f1 f2 rel b moveFocus >>= return
validateProof' proof@(Trans ctx rel f1 f f2 p1 p2) moveFocus = 
    getStart p1 >>= whenEqWithDefault err f1 >>
    getEnd p1 >>= whenEqWithDefault err f >>
    getStart p2 >>= whenEqWithDefault err f >>
    getEnd p2 >>= whenEqWithDefault err f2 >>
    validateProof' p1 (goDownL' . moveFocus) >>= \p1' ->
    validateProof' p2 (goDownR' . moveFocus) >>= \p2' ->
    return (mappend p1' p2')
    
    where err :: ProofError
          err = ProofError (TransInconsistent proof) moveFocus
    
validateProof' proof@(Deduc ctx p q prf) mvFocus = 
    getEnd prf >>= whenEqWithDefault err q >>
    case (addHypothesisProof (PE.toExpr p) relEquiv [true'] prf) of
      Nothing -> Left err
      Just prf' -> validateProof' prf' mvFocus >> return proof
    where err = ProofError DeducInvalidEnd mvFocus
          Expr true' = true
validateProof' _ _ = undefined


possibleExpr :: PE.PreExpr -> Basic -> [(PE.PreExpr, Maybe PE.Focus)]
possibleExpr p basic = 
            case basic of
                Evaluate -> filter (flip ((/=) . fst) p) [(evalExpr p,Nothing)]
                _ -> map ((PE.toExpr &&& Just) . fst) . rights $ concatMap (rewriteAllFocuses p) (truthRules basic)

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
newProof :: Maybe Ctx -> Relation -> PE.Focus -> PE.Focus -> Proof
newProof = Hole . maybe beginCtx id


-- | Comenzamos una prueba dada la expresion inicial y la relacion.
newProofWithStart :: Relation -> PE.Focus -> Proof
newProofWithStart rel f = Hole beginCtx rel f PE.emptyExpr

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
holeProof :: Maybe Ctx -> Relation -> Proof
holeProof c r = newProof c r PE.emptyExpr PE.emptyExpr

-- | ProofFocus vacio
emptyProof :: Maybe Ctx -> Relation -> ProofFocus
emptyProof c r = toProofFocus $ holeProof c r

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
newProofWithoutEnd r f hi = Hole beginCtx r f h
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
          ctx = beginCtx 

{- | Comenzamos una prueba por casos. -}

newProofWithCases :: Relation -> PE.Focus -> PE.Focus -> PE.Focus -> [PE.Focus] -> Proof
newProofWithCases r f f' c lc = Cases ctx r f f' c lp
    where ctx :: Ctx
          ctx = ctxFromList lc
          lp :: [(PE.Focus, Proof)]
          lp = [] -- map (\fi@(ei,_) -> (fi, Hole (beginCtx ei) r f f')) lc


-- | Función para convertir una prueba en un Hole
toHoleProof :: ProofFocus -> ProofFocus
toHoleProof (p@(Simple ctx r f f' b),path) = (Hole ctx r f f',path)
toHoleProof (p@(Trans ctx r f f' f'' p1 p2),path) = (Hole ctx r f f'',path)
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
    (Trans ctx r f1 PE.emptyExpr f2 (Hole ctx r f1 PE.emptyExpr) (Hole ctx r PE.emptyExpr f2),path)
-- Si le pasamos una prueba simple, la considera un hueco
addEmptyStep (p@(Simple ctx r f1 f2 b),path) = 
    (Trans ctx r f1 PE.emptyExpr f2 (Hole ctx r f1 PE.emptyExpr) (Hole ctx r PE.emptyExpr f2),path)
addEmptyStep p = p


createEmptyStep :: Proof -> Proof
createEmptyStep (Hole ctx r f1 f2) = 
    Trans ctx r f1 PE.emptyExpr f2 (Hole ctx r f1 PE.emptyExpr) (Hole ctx r PE.emptyExpr f2)
-- Si le pasamos una prueba simple, la considera un hueco
createEmptyStep (Simple ctx r f1 f2 b) = 
    Trans ctx r f1 PE.emptyExpr f2 (Hole ctx r f1 PE.emptyExpr) (Hole ctx r PE.emptyExpr f2)
createEmptyStep p = p


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

addBoolHypothesis :: PE.PreExpr -> Ctx -> (Ctx,Maybe Name)
addBoolHypothesis e = addHypothesis e relEquiv [true']
    where Expr true' = true
