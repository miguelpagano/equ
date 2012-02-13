{-# Language Rank2Types,TypeSynonymInstances #-}
module Equ.Proof.ListedProof
    (ListedProof'(..),ListedProof,createListedProof
    ,addStepOnPosition,updateSelExpr, updateRelLP, updateBasicLP
    ,moveToPosition,moveToNextPosition, moveToPrevPosition
    ,getSelExpr,getSelBasic,getRelLP, addStepOnPositionM
    ) where

import Equ.Proof.Proof
import Equ.Proof.Monad(PM)
import Equ.Proof.Zipper
import Equ.Rule(Relation)

import qualified Equ.PreExpr as PE

import Data.Maybe(fromJust)
import Data.Functor.Identity


{- Un ListedProof nos sirve para ver una prueba transitiva como una lista de pasos
simples.
Para utilizar este tipo, lo creamos a partir de una prueba transitiva, y luego
podemos ir reemplazando pasos simples o huecos por más transitividades, es decir, 
podemos reemplazar el elemento i-ésimo de la lista, en dos nuevos elementos (que corresponden
a la prueba izquierda y derecha de la nueva transitividad que queda en ese lugar).
-}

data ListedProof' ctxTy relTy proofTy exprTy= ListedProof' {
                    pList  :: [Proof' ctxTy relTy proofTy exprTy]
                  , pFocus :: ProofFocus' ctxTy relTy proofTy exprTy
                  , selIndex :: Int -- indice del elemento seleccionado
}

createListedProof :: ProofFocus' ctxTy relTy proofTy exprTy -> 
                     Maybe (ListedProof' ctxTy relTy proofTy exprTy)
createListedProof pf = let pf' = goTop' pf in
                           case (fst pf') of
                                (Simple _ _ _ _ _) -> Just $ lSimple pf'
                                (Trans _ _ _ _ _ _ _) -> Just $ lTrans pf'
                                _ -> Nothing
                                
    where lSimple pfocus = ListedProof' {
                            pList = [fst pfocus]
                          , pFocus = pfocus
                          , selIndex = 0
                          }
          lTrans pfocus = ListedProof' {
                            pList = createListedProof' [fst focusOnLeft] focusOnLeft
                          , pFocus = focusOnLeft
                          , selIndex = 0
                          }
            where focusOnLeft = goLeftLeaf pfocus
                            

createListedProof' :: [Proof' ctxTy relTy proofTy exprTy] ->
                      ProofFocus' ctxTy relTy proofTy exprTy -> 
                      [Proof' ctxTy relTy proofTy exprTy]
createListedProof' ps pf = let mpf = goNextStep' pf in
                               case mpf of
                                    Nothing -> ps
                                    Just pf' -> createListedProof' (ps++[fst pf']) pf'
                                    
{- Transforma una prueba simple o hueco, que tenemos en la lista, en dos nuevos huecos y 
   actualiza el proofFocus, creando la nueva transitividad correspondiente.
   La función fNewProofs toma el paso de la prueba que queremos transformar y devuelve
   una nueva expresion y dos nuevos pasos, así se puede construir la transitividad.
   Dejamos enfocado la parte derecha de esa transitividad.
   Las funciones fUpIndexExpr y fUpIndexBasic toman las expresiones y el basic de un paso
   de prueba respectivamente, el nuevo indice que tiene ese paso, y debe actualizar
   algun componente relacionado con el indice del paso en la lista.-}

addStepOnPositionM :: Monad m => Int -> 
                     (Proof' ctxTy relTy proofTy exprTy -> 
                     (exprTy,Proof' ctxTy relTy proofTy exprTy,Proof' ctxTy relTy proofTy exprTy)) ->
                     (exprTy -> Int -> m exprTy) -> (proofTy -> Int -> m proofTy) ->
                     ListedProof' ctxTy relTy proofTy exprTy -> 
                     m (ListedProof' ctxTy relTy proofTy exprTy)
addStepOnPositionM ind fNewProofs fUpIndexExpr fUpIndexBasic lProof = 
                                if ind < 0 || ind >= length (pList lProof)
                                then return lProof
                                else updateStepIndexesM fUpIndexExpr fUpIndexBasic
                                            (ind+2) $
                                            ListedProof' {
                                                pList = take ind (pList lProof) ++ 
                                                newSteps nPFocus ++ drop (ind+1) (pList lProof)
                                            , pFocus = newFocus nPFocus
                                            , selIndex = ind + 1
                                            }
                                  
    where nPFocus = (moveToPos ind $ pFocus lProof)
          
          newSteps pf = [snd' (fNewProofs $ fst pf),third (fNewProofs $ fst pf)]
                                  
          newFocus (p,path) = goDownR' (Trans ctx rel expr1 newExpr expr2 p1 p2,path)
            where   ctx = fromJust $ getCtx p
                    rel = fromJust $ getRel p
                    expr1 = fromJust $ getStart p
                    expr2 = fromJust $ getEnd p
                    newExpr = fst' $ fNewProofs p
                    p1 = snd' $ fNewProofs p
                    p2 = third $ fNewProofs p


addStepOnPosition :: Int -> (Proof' ctxTy relTy proofTy exprTy -> 
                    (exprTy,Proof' ctxTy relTy proofTy exprTy,Proof' ctxTy relTy proofTy exprTy)) ->
                    (exprTy -> Int -> exprTy) -> (proofTy -> Int -> proofTy) ->
                    ListedProof' ctxTy relTy proofTy exprTy -> 
                    (ListedProof' ctxTy relTy proofTy exprTy)

addStepOnPosition ind fNewProofs fUpIndexExpr fUpIndexBasic = runIdentity .
                                                              addStepOnPositionM ind fNewProofs 
                                                                                     (\i -> return . fUpIndexExpr i) 
                                                                                     (\i -> return . fUpIndexBasic i) 
                                                                                            

updateStepIndexesM :: Monad m => (exprTy -> Int -> m exprTy) -> (proofTy -> Int -> m proofTy) ->
                     Int ->  ListedProof' ctxTy relTy proofTy exprTy -> 
                     m (ListedProof' ctxTy relTy proofTy exprTy)
updateStepIndexesM fUpExpr fUpBasic ind lProof = do
  let oldList = take ind (pList lProof)
  newList <- mapM (updateList ind) $ drop ind $ pList lProof
  newFocus <- updateFocus (pFocus lProof) ind
  return $ ListedProof' {
               pList = oldList ++ newList
             , pFocus = moveToPos (ind-1) newFocus
             , selIndex = ind-1
             }
        
    where updateList idx p = 
              case p of
                   (Hole _ _ _ _) -> do 
                       p' <- proofStartUpdated p idx
                       proofEndUpdated p' idx
                   (Simple _ _ _ _ _) -> do 
                       p' <- fUpBasic (fromJust $ getBasic p) idx
                       p'' <- proofStartUpdated p idx
                       newPrf <- proofEndUpdated p'' idx
                       return (updateBasic newPrf p')

          updateFocus pf ind = do
              let (p,path) = moveToPos ind pf 
              pint <- proofStartUpdated p ind
              p' <- proofEndUpdated pint ind    
              case p of
                (Hole _ _ _ _) -> case goNextStep' (p',path) of
                      Nothing -> return (p',path)
                      Just pf' -> updateFocus pf' (ind+1)
                (Simple _ _ _ _ _) -> do
                        pint' <- fUpBasic (fromJust $ getBasic p') ind
                        p'' <- return $ updateBasic p' pint'
                        case goNextStep' (p'',path) of
                           Nothing -> return (p'',path)
                           Just pf' -> updateFocus pf' (ind+1)


          proofStartUpdated p i = fUpExpr (fromJust $ getStart p) i >>= 
                                  return . updateStart p
          
          proofEndUpdated p i = fUpExpr (fromJust $ getEnd p) i >>=
                                return . updateEnd p 

                                    
-- Reemplaza la expresión derecha de un paso de la prueba. Deja enfocado el paso.
updateSelExpr :: exprTy -> ListedProof' ctxTy relTy proofTy exprTy ->
                 ListedProof' ctxTy relTy proofTy exprTy
updateSelExpr expr lProof = let ind = selIndex lProof in
                            ListedProof' {
                                pList = take ind (pList lProof) ++
                                    [updateEnd ((pList lProof)!!ind) expr] ++
                                    drop (ind+1) (pList lProof)
                              , pFocus = nPFocus
                              , selIndex = ind
                            }
                            
    where nPFocus = let up1 = updateEndFocus (goFirstLeft $ pFocus lProof) expr in
                        case goRight (fromJust up1) of
                             Nothing -> goEnd (fromJust up1)
                             Just pf' -> goEnd $ goDownL' $ fromJust $ updateMiddleFocus (goUp' $ fromJust $ updateStartFocus pf' expr) expr
                             
getSelExpr :: ListedProof' ctxTy relTy proofTy exprTy -> exprTy
getSelExpr lProof = fromJust $ getEnd ((pList lProof)!!(selIndex lProof))

getSelBasic :: ListedProof' ctxTy relTy proofTy exprTy -> Maybe proofTy
getSelBasic lProof = getBasic ((pList lProof)!!(selIndex lProof))


getRelLP :: ListedProof' ctxTy relTy proofTy exprTy -> relTy
getRelLP lProof = fromJust $ getRel ((pList lProof)!!(selIndex lProof))

updateRelLP :: ListedProof' ctxTy relTy proofTy exprTy -> relTy ->
               ListedProof' ctxTy relTy proofTy exprTy
updateRelLP lProof rel = let ind = selIndex lProof in
                         lProof {
                            pList = take ind (pList lProof) ++
                             [updateRel ((pList lProof)!!ind) rel] ++
                             drop (ind+1) (pList lProof)
                          , pFocus = (updateRel (fst $ pFocus lProof) rel,snd (pFocus lProof))
                         }
                         
updateBasicLP :: ListedProof' ctxTy relTy proofTy exprTy -> proofTy ->
                 ListedProof' ctxTy relTy proofTy exprTy
updateBasicLP lProof basic = let ind = selIndex lProof in
                             case ((pList lProof)!!ind) of
                                  (Hole c r e1 e2) ->
                                    lproofRet c r e1 e2 ind
                                  (Simple c r e1 e2 b) ->
                                    lproofRet c r e1 e2 ind
                                  _ -> lProof
                                  
    where lproofRet c r e1 e2 ind = 
            lProof {
                  pList = take ind (pList lProof) ++
                    [(Simple c r e1 e2 basic)] ++
                    drop (ind+1) (pList lProof)
                , pFocus = (Simple c r e1 e2 basic,snd (pFocus lProof))
                }
                 
                
moveToPosition :: Int -> ListedProof' ctxTy relTy proofTy exprTy ->
                  ListedProof' ctxTy relTy proofTy exprTy
moveToPosition i lProof = if i < 0 || i > length (pList lProof)
                             then lProof
                             else ListedProof' {
                                    pList = pList lProof
                                  , pFocus = moveToPos i (pFocus lProof)
                                  , selIndex = i
                             }
                             
moveToNextPosition :: ListedProof' ctxTy relTy proofTy exprTy ->
                      ListedProof' ctxTy relTy proofTy exprTy
moveToNextPosition lProof = if selIndex lProof >= length (pList lProof)
                               then lProof
                               else lProof {selIndex = (selIndex lProof) + 1}
                               
moveToPrevPosition :: ListedProof' ctxTy relTy proofTy exprTy ->
                      ListedProof' ctxTy relTy proofTy exprTy
moveToPrevPosition lProof = if selIndex lProof == 0
                               then lProof
                               else lProof {selIndex = (selIndex lProof) - 1}
    
moveToLastPosition :: ListedProof' ctxTy relTy proofTy exprTy ->
                      ListedProof' ctxTy relTy proofTy exprTy
moveToLastPosition lProof = let lind = length (pList lProof) - 1 in
                                moveToPosition lind lProof
                    
-- Mueve un proofFocus hasta la hoja indicada por el indice. 
-- NOTA: Si el indice es mayor a la cantidad de hojas devuelve la ultima.
moveToPos :: Int -> ProofFocus' ctxTy relTy proofTy exprTy -> 
             ProofFocus' ctxTy relTy proofTy exprTy
moveToPos 0 pf = goLeftLeaf $ goTop' pf
moveToPos n pf = goNextStep (moveToPos (n-1) pf)
                      
                      
fst' :: (a,b,c) -> a
fst' (a,_,_) = a

snd' :: (a,b,c) -> b
snd' (_,b,_) = b

third :: (a,b,c) -> c
third (_,_,c) = c
                                    
                                    
type ListedProof = ListedProof' Ctx Relation Basic PE.Focus
                                    
instance Show ListedProof where
    show lProof = show (pFocus lProof)