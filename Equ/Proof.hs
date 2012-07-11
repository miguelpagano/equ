{-# Language GADTs,OverloadedStrings #-}

{-| Este m&#243;dulo define la noci&#243;n de una prueba. -}
module Equ.Proof ( newProof
                 , newProofWithCases
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
                 , Proof
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
                 , printProof
                 ) where

import Equ.Proof.Annot
import Equ.Proof.Proof hiding (getCtx,getStart,getEnd,getRel,setCtx)
import qualified Equ.Proof.Proof as P(getStart,getEnd,getBasic,getRel)
import Equ.Proof.Zipper
import Equ.Proof.Monad
import Equ.Proof.Error
import Equ.Proof.ListedProof
import Equ.Theories.Common hiding (and)
import Equ.Theories.FOL(folOr)
import Equ.TypeChecker(typeCheckPreExpr)
import Equ.Syntax hiding (Hole)

import qualified Equ.PreExpr as PE hiding (replace)
import Equ.Expr
import Equ.PreExpr.Eval (evalExpr)
import Equ.Rule
import Equ.Rewrite

import Equ.Types (Type)
import Equ.TypeChecker (checkPreExpr)
import Equ.IndType
import Equ.IndTypes
import Equ.Theories

import Equ.Proof.Induction(createIndHypothesis)

import Data.Monoid(mappend)

import Data.Maybe
import Data.Either (partitionEithers,rights)
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.List (find)
import Data.Function (on)
import Control.Monad
import Control.Arrow((&&&),(***))
import Control.Applicative ((<$>))

import System.IO.Unsafe(unsafePerformIO)

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
checkEval = (==) `on` (evalExpr . PE.toExpr)


-- Funcion para checkear igualdad, con la variante importante que en caso de
-- no cumplirse devolvemos un resultado por default.
checkEqWithDefault :: Eq a => ProofError -> a -> a -> PM ()
checkEqWithDefault def a b | a /= b = Left def
                           | otherwise = return ()

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
    whenEqRelWithDefault errRel rel (truthRel t) [relEquiv,relEq] >>
    case partitionEithers $ rewriteAllFocusesInformative (PE.toExpr f1) rule of
         (_,[]) -> Left err
         (_,ls) -> case partitionEithers $ map checkeq ls of
                        (errors,[]) -> Left $ head errors
                        (_,xs) -> let funConds = map conditionFunction (truthConditions t) in
                                      case partitionEithers $ map (checkConds funConds) xs of
                                           (errors,[]) -> Left $ head errors
                                           (_xs) -> return . snd' $ head xs
    where 
        errRel :: ProofError
        errRel = ProofError (ClashRel rel (truthRel t)) fMove
        err :: ProofError
        err = ProofError (BasicNotApplicable $ truthBasic t) fMove
        checkeq :: (PE.Focus,PE.Focus,PE.ExprSubst) -> PM (PE.Focus,PE.Focus,PE.ExprSubst)
        checkeq t@(f1',f2',s) = 
            return (f1',f2') >>=
            whenEqWithDefault' err (PE.goTop f2) fst . (PE.goTop *** id) >>
            return t
        checkConds :: [(PE.ExprSubst -> PE.PreExpr -> Bool)] ->
                      (PE.Focus,PE.Focus,PE.ExprSubst) ->
                      PM (PE.Focus,PE.Focus,PE.ExprSubst)
        -- Chequeamos que la substitucion resultante satisfaga todas las condiciones
        -- de aplicación de la regla
        checkConds fConds t@(_,_,subst) = whenPM (\(_,_,subst) ->
                                  and $ invMap fConds (subst,PE.toExpr f1)) errorCondition t
        invMap :: [(a -> b -> c)] -> (a,b) -> [c]
        invMap [] (_,_) = []
        invMap (f:fs) (a,b) = (f a b):(invMap fs (a,b))
        thrd :: (a,b,c) -> c
        thrd (_,_,c) = c
        snd' (_,b,_) = b
        errorCondition = ProofError (BasicConditionError (truthBasic t)) fMove
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
validateStepProof lProof = let p = (pList lProof)!!(selIndex lProof) 
                           in validateProof p
                          
validateProof :: Proof -> PM Proof
validateProof p = validateProof' p goTop'
                          
validateProof' :: Proof -> (ProofFocus -> ProofFocus) -> PM Proof
validateProof' (Hole ctx rel f1 f2) moveFocus = Left $ ProofError HoleProof moveFocus
validateProof' proof@(Simple ctx rel f1 f2 b) moveFocus = 
    proofFromTruth f1 f2 rel b moveFocus
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
                    
          
-- Falta ver que las variables de un pattern sean frescas respecto a las expresiones
-- de la prueba, donde reemplazamos la variable inductiva por una constante.
validateProof' proof@(Ind ctx rel f1 f2 e ps) _ =
    either (const $  Left errProof) (return . PE.toFocus) 
        (typeCheckPreExpr (PE.toExpr f1)) >>= \typedF1 ->
    -- Primero verificamos que e sea variable:
    PE.isVar (ProofError (InductionError IndInNotVar) id) (PE.toExpr e) >>= \x ->
    -- Luego vemos que la variable esté en la expresión f1
    whenPM' (Set.member x (PE.freeVars (PE.toExpr typedF1)))
            (ProofError (InductionError VarIndNotInExpr) id) >>
    -- Chequeamos los casos de inducción:
    checkPatterns x proof ps >>
    return proof
    
    where checkPatterns :: Variable -> Proof -> [(PE.Focus,Proof)] -> PM ()
          checkPatterns x pr ps = flip (maybe (Left $ ProofError (InductionError TypeNotInductive) id)) 
                                  (getIndType (varTy x)) $
                                  \it ->
                                  return (splitByConst (varTy x) ps) >>= 
                                  \(constPat,basePat,indPat) ->
                                  -- chequeamos las variables de cada pattern
                                  mapM (checkVarsPattern x pr) (map fst basePat) >>
                                  mapM (checkVarsPattern x pr) (map fst indPat) >>
                                  checkSubProof x pr constPat >>
                                  checkSubProof x pr basePat >>
                                  checkSubProofInd x pr indPat >>
                                  checkAllConstants it constPat >>
                                  checkAllBaseConst it basePat >>
                                  checkAllIndConst it indPat


          -- Esta funcion chequea las pruebas de cada tipo de patrón base
          -- (no aplica hipótesis inductiva).
          checkSubProof x pr cs = mapM_ go cs 
              where go (expr,p) = 
                            -- Chequeamos que la prueba p demuestra lo mismo que pr, pero
                            -- aplicando la substitucion correspondiente
                            sameProofWithSubst p pr (Map.singleton x (PE.toExpr expr)) >>
                            sameCtxs pr p >>
                            -- Finalmente validamos la prueba p y continuamos chequeando.
                            validateProof' p id
                             
          
          checkSubProofInd x pr cs = Map.elems <$> getCtx proof >>= \hypsProof ->
                                     mapM_ (go hypsProof) cs
              where go hprf (expr,p) = 
                        let hyp = fromJust $ createIndHypothesis rel f1 f2 expr x "HI" in
                        -- Chequeamos que cada hipótesis del contexto de la subprueba
                        -- esté en el contexto de la prueba inductiva, o sea hipótesis
                        -- inductiva.
                        Map.elems <$> getCtx p >>= 
                        \hypsSubProof -> whenPM' (foldl (\b h -> b && elem h hprf || h == hyp) True hypsSubProof)
                                        (ProofError (InductionError SubProofHypothesis) id) >>
                        -- Ahora vemos que la subprueba prueba lo mismo que la prueba inductiva,
                        -- pero reemplazando la variable por el pattern correspondiente.
                        sameProofWithSubst p pr (Map.singleton x (PE.toExpr expr)) >>
                        validateProof' p id


          -- Controlamos que todos los constructores (0-arios, unarios y binarios) 
          -- usados en una prueba correspondan al tipo inductivo.
          checkConstructor :: Ord a => PErrorInduction -> 
                             (PE.PreExpr -> Maybe a) -> (IndType -> [a]) -> 
                             IndType -> [(PE.Focus,Proof)] -> PM ()
          checkConstructor err get els it ps = whenPM' (elsInProof `isSublistOf` els it) 
                                               (ProofError (InductionError err) id)
              where elsInProof = catMaybes $ map (get . PE.toExpr . fst) ps
          
          checkAllConstants :: IndType -> [(PE.Focus,Proof)] -> PM ()
          checkAllConstants = checkConstructor ConstantPatternError PE.getConstant constants
                    
          checkAllBaseConst = checkConstructor OperatorPatternError PE.getOperator baseConstructors
          
          checkAllIndConst = checkConstructor OperatorPatternError PE.getOperator indConstructors
          
          -- Chequeamos que un pattern no contiene variables que estén en las
          -- expresiones originales (salvo que sea la misma variable inductiva).
          checkVarsPattern :: Variable -> Proof ->  PE.Focus -> PM ()
          checkVarsPattern v p pattern = 
              getStart p >>= \fs -> getEnd p >>= \fe ->
              return (Set.map varName $ PE.freeVars $ PE.toExpr fs) >>= 
              \varNames1 ->
              return (Set.map varName $ PE.freeVars $ PE.toExpr fe) >>=
              \varNames2 -> 
              return (Set.delete (varName v) $ Set.union varNames1 varNames2) >>= \varNames ->
              return (Set.map varName $ PE.freeVars $ PE.toExpr pattern) >>= 
              \varNamesPattern ->
              whenPM' (Set.notMember True $ Set.map (flip Set.member varNames) varNamesPattern)
                      (ProofError (InductionError VariablePatternError) id)
              
              
              
              
              
-- | Validación de una prueba por casos. La prueba de exahustividad de las guardas
--   es opcional. Ver como podemos dar un mensaje Warning en ese caso.
validateProof' proof@(Cases ctx rel f1 f2 e cases mGuardsProof) _ =
    -- Primero chequeamos la prueba que dice que el "o" de las guardas vale:
    case mGuardsProof of
         Just guardsProof -> checkGuardsProof guardsProof
         Nothing -> return proof
    >>
    -- Ahora debemos chequear cada prueba de casos. Cada subprueba debe tener
    -- la misma relacion, expresion inicial y final que la prueba general, solo
    -- que agrega al contexto la hipótesis correspondiente al caso, por ejemplo
    -- si el caso es "e==0", luego se agrega "e==0 ≡ True" como hipótesis.
    foldl (>>) (return ()) (map (checkSubProofCases proof) cases) >>
    return proof

    
    
    -- Chequeamos la prueba que demuestra que el "o" de todas las guardas es True.
    -- Para eso, esta prueba debe tener el mismo contexto que la prueba general.
    -- debe tener como relación a la equivalencia, la expresión inicial debe ser
    -- el o de todas las guardas (VER QUE PASA SI ES LA MISMA EXPRESION PERO CON CONMUTATIVIDAD
    -- Y ASOCIATIVIDAD DISTINTOS) y la expresión final debe ser True.
    where checkGuardsProof guardsProof=
            getRel guardsProof >>= \relGP -> getStart guardsProof >>= \stGP -> 
            getEnd guardsProof >>= \endGP -> return (map fst cases) >>= \cs -> 
            orCasesExpr cs >>= \orCE -> 
            sameCtxs guardsProof proof >>
            whenPM' (relGP==relEquiv) errProof >> 
            whenPM' (stGP==orCE) errProof >>
            whenPM' (endGP==(PE.toFocus $ PE.Con folTrue)) errProof >>
            validateProof' guardsProof id
            
          orCasesExpr :: [PE.Focus] -> PM PE.Focus  
          orCasesExpr [] = Left $ ProofError (CasesError EmptyCases) id -- La lista de casos no puede ser vacia
          orCasesExpr fs = Right $ PE.toFocus $ orCasesExpr' (map PE.toExpr fs)
          
          orCasesExpr' [e] = e
          orCasesExpr' (e:es) = PE.BinOp folOr e (orCasesExpr' es)
          
          checkSubProofCases :: Proof -> (PE.Focus,Proof) -> PM ()
          checkSubProofCases proof (c,cProof) =
              sameProof proof cProof >>
              getCtx cProof >>= \cpCtx ->
              getCtx proof >>= \ctx ->
              return (freshName cpCtx) >>= \name -> return (createHypothesis name (Expr $ PE.toExpr c) []) >>=
              \hypCase -> (return $ Map.elems ctx) >>= \hypsProof ->
              (return $ Map.elems cpCtx) >>= \hypsCasesProof ->
              whenPM' (and $ map (\h -> elem h hypsProof || h==hypCase) hypsCasesProof)
                      (ProofError (CasesError HypothesisCases) id) >>
              validateProof' cProof id >> return ()
              
validateProof' _ _ = undefined

-- | Chequea que los contextos de dos pruebas sean iguales.
sameCtxs :: Proof -> Proof -> PM ()
sameCtxs = liftA2' (checkEqWithDefault (ProofError ContextsNotEqual id)) `on` getCtx

                    
-- | Chequea que dos pruebas tengan la misma relación
sameRelation :: Proof -> Proof -> PM ()
sameRelation = liftA2' (checkEqWithDefault  (ProofError RelNotEqual id)) `on` getRel

-- | Esta función verifica si dos pruebas prueban lo mismo, aunque no sean la misma prueba.
--   Esto es, que tengan las mismas expresiones inicial y final, y la misma relacion. Podrían
--   tener diferentes contextos.
--   Si se verifica, retorna Right (), caso contrario Left error.
sameProof :: Proof -> Proof -> PM ()
sameProof p1 p2 =
    getStart p1 >>= \p1st -> getEnd p1 >>= \p1end -> 
    getRel p1 >>= \rel1 -> getStart p2 >>= \p2st -> 
    getEnd p2 >>= \p2end ->
    getRel p2 >>= \rel2 ->
    whenPM' (p1st==p2st && p1end==p2end && rel1==rel2) (ProofError (InductionError IncorrectSubProof ) id)


-- | Chequea que dos pruebas prueban lo mismo, aplicando en las expresiones de
--   la segunda la substitución dada.
sameProofWithSubst :: Proof -> Proof -> PE.ExprSubst -> PM ()
sameProofWithSubst p1 p2 subst = 
        getStart p2 >>= \p2start -> 
        getEnd p2 >>= \p2end ->
        return (updateStart p2 (PE.toFocus $ PE.applySubst (PE.toExpr p2start) subst)) >>= \p2' ->
        return (updateEnd p2' (PE.toFocus $ PE.applySubst (PE.toExpr p2end) subst)) >>= \p2'' ->
        sameProof p1 p2''
                

-- | Devuelve las posibles expresiones de aplicar una 
possibleExpr :: PE.PreExpr -> Basic -> [(PE.PreExpr, Maybe PE.Focus)]
possibleExpr p basic = 
            case basic of
                Evaluate -> filter (flip ((/=) . fst) p) [(evalExpr p,Nothing)]
                _ -> map ((PE.toExpr &&& Just) . fst) . typed $ concatMap (rewriteAllFocuses p) (truthRules basic)
    where typed = filter (isRight . checkPreExpr . PE.toExpr . fst) . rights
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
newProofWithCases :: Relation -> PE.Focus -> PE.Focus -> PE.Focus -> [PE.Focus] -> Maybe Proof -> Proof
newProofWithCases r f f' c lc orGuardsProof = Cases ctx r f f' c lp orGuardsProof
    where
        ctx :: Ctx
        ctx = ctxFromList lc
        lp :: [(PE.Focus,Proof)]
        lp = []


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
   
-- | Dada una prueba, retorna la expresión que representa a toda la prueba.
getExprProof :: PM Proof -> Expr
getExprProof = either (const holeExpr) buildExpr
    where buildExpr p = Expr $ PE.BinOp (relToOp . fromJust $ P.getRel p)
                                     (PE.toExpr . fromJust $ P.getStart p)
                                     (PE.toExpr . fromJust $ P.getEnd p)


-- Probablemente esta función sea más eficiente que @l1 `elem` permutations l2@.
-- Sería interesante chequearlo; también habría que moverlo a un lugar más 
-- apropiado.
isSublistOf :: Ord a => [a] -> [a] -> Bool
isSublistOf = Set.isSubsetOf `on` Set.fromList

liftA2' :: (a -> b -> PM c) -> PM a -> PM b -> PM c
liftA2' f ma mb = ma >>= \a -> mb >>= f a