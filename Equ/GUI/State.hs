{-# Language OverloadedStrings , RankNTypes #-}
-- | Utilidades varias que tienen que ver con el estado de la
-- interfaz (es probable que se muden a Equ.GUI.State) y con
-- funciones convenientes que podrían mudarse a otros módulos.
module Equ.GUI.State (-- * Proyeccion de componentes del estado
                       getSymFrame
                     , getParentNamed
                     , getWindow
                     , getAxiomFrame
                     , getErrPane
                     , getErrPanedLabel
                     , getFrmCtrl
                     , getExprWidget
                     , eventWithState
                     , getTreeExprBox
                     , getSymCtrl
                     , getFormPane
                     , getExpr
                     , getFocusedExpr
                     , getAxiomCtrl
                     , getAxiomBox
                     , getAxiomBox'
                     , getExprState
                     , getUndoList
                     , getValidProof
                     , getExprProof
                     , getProof
                     , getRedoList
                     , getRelPF
                     , getProofState
                     , getSelectedExpr
                     , getProofWidget
                     , getStepProofBox
                     -- * Modificacion del estado.
                     , updateExpr
                     , updateFrmCtrl
                     , updateQVar
                     , updateFocus
                     , updateUndoList
                     , updateValidProof
                     , updateExprWidget
                     , updateProof
                     , addTheorem
                     , addToRedoList
                     , addToUndoListFromRedo
                     , updateRedoList
                     , updateProofWidget
                     , updateProofNoUndo
                     , updateAxiomBox
                     , setUndoing
                     , setNoUndoing
                     -- * Otras funciones
                     , showExpr
                     , withState
                     , localPath
                     , checkValidProof
                     , initialState
                     , cleanTreeExpr
                     -- * Funciones relacionadas con arbol de tipos
                     , addAtomExprTree
                     , addQuantExprTree
                     , getMainExprTree
                     , getOpExprTree
                     , getQuantExprTree
                     , getTreeOpBox
                     , getTreeQuantBox
                     , getTreeVarQBox
                     , searchFocusInTree
                     , selectTypeFromBox
                     , updateExprSelectExpr
                     , updateMainExprTree
                     , updateMainExprTreeType
                     , updateOpExprTree
                     , updateTypeAtomInExprTree
                     , updateTypeAtomInMainExprTree
                     , updateTypeOpInMainExprTree
                     , updateTypeQuantInExprTree
                     , updateTypeQuantInMainExprTree
                     , updateTypeSelectType
                     , updateTypeVarQInMainExprTree
                     -- * Funciones relacionadas con pruebas
                     , updateProofState 
                     , unsetProofState
                     , updateExprState
                     --, changeProofFocus
                     , updateRelation
                     , updateSelectedExpr
                     , restoreValidProofImage
                     , updateImageValid
                     -- * Manipulación del contexto global
                     , getGlobalCtx
                     , getGlobalHypothesis
                     , addGlobalHypothesis
                     , module Control.Monad.State.Strict
                     )
    where

import Equ.GUI.Types
import Equ.GUI.Utils

import Equ.Expr
import Equ.PreExpr hiding(goUp,goRight,goLeft,goDown,goDownL)
import Equ.Theories
import Equ.Syntax
import Equ.Parser

import Equ.Proof(addBoolHypothesis)
import Equ.Proof.Proof
import Equ.Proof.Error(errEmptyProof)
import Equ.Proof(ProofFocus,ProofFocus',updateStartFocus,updateEndFocus,PM,validateProof,
                 toProof,goFirstLeft,updateMiddleFocus,goUp',getEndFocus,goRight,goEnd,goDownL',
                  getBasicFocus)
import Equ.Rule

import Equ.Types

import Graphics.UI.Gtk hiding (eventButton, eventSent, get)

import qualified Graphics.UI.Gtk as G
import System.Glib.GType
import System.Glib.GObject

import Data.Text (unpack)
import Data.List

import Data.Reference
import Control.Arrow(first,second,(***),(&&&))
import Data.Maybe(fromJust)
import Control.Monad(liftM,when)
import Control.Monad.State.Strict(get,put,evalStateT)
import Control.Monad.Trans(liftIO)

import qualified Data.Serialize as S
import qualified Data.ByteString as L
import qualified Data.Foldable as F (mapM_,forM_) 

{- Funciones que tienen que ver con el estado -} 
-- | Devuelve el estado.
askRef :: IState GState
askRef = get >>= readRef

-- | Devuelve el estado y la referencia.
askRef' :: IState (GState, GRef)
askRef' = get >>= \r -> readRef r >>= \s -> return (s,r)

-- | Consulta el estado y lo aplica a una computación con efectos.
withRefValue :: (GState -> IO a) -> IState a
withRefValue f = get >>= readRef >>= liftIO . f

-- | Consulta el estado, lo modifica de acuerdo al argumento y el
-- resultado de esta función pasa a ser el nuevo estado.
update :: (GState -> GState) -> IRG
update f = get >>= \r -> readRef r >>= 
                        writeRef r . f >>
                        put r

-- | Realiza una acción en un estado modificado y luego vuelve al estado
-- anterior; devuelve el resultado de la acción.
local :: (GState -> IO a) -> IState a
local f = askRef >>= \s -> liftIO (f s) >>= \a -> update (const s) >> return a


-- | Realiza una acción en un estado modificado y luego vuelve al estado
-- anterior; devuelve el resultado de la acción.
local' :: (GState -> IState a) -> IState a
local' f = askRef >>= \oldState -> f oldState >>= \a -> 
           getExpr >>= \e ->
           io (debug ("Local:" ++ show e)) >>
           update (const oldState) >> return a

-- | Versión especializada de la anterior donde lo que se modifica es
-- el path.
localPath :: Move -> (Move -> IState a) -> IState a
localPath p' act = local' (\st -> act (p' . goTop))


-- | Actualiza el mensaje que se muestra en el área de estado.
updateStatus :: String -> IState ()
updateStatus msg = withRefValue (\s -> putMsg (status s) msg) 


-- | Actualiza la expresión que se muestra en el área de estado;
-- esta es una función que puede dejar de tener sentido más adelante.
showExpr :: IState ()
--showExpr = withRefValue $ uncurry putMsg . (status &&& show . toExpr . (fExpr . fromJust . gExpr) )
showExpr = getProofState >>= 
           F.mapM_ (\ps -> showProof) -- DEJO ESTO ASI PORQUE SI NO NO ME DOY CUENTA SI ACTUALIZO BIEN LA EXPRESION DENTRO DE LA PRUEBA

showProof :: IState ()
showProof = withRefValue $ uncurry putMsg . (status &&& show . proof . fromJust . gProof )


showProof' = getProof >>= liftIO . debug . show

{- Las tres funciones que siguen actualizan componentes particulares
del estado. -}
-- | Pone una nueva expresión en el lugar indicado por la función de ida-vuelta.
updateExpr e' p = update (updateExpr' e' p) >> showExpr >> addToUndoList >> restoreValidProofImage

updateExpr'' :: Move -> (PreExpr -> PreExpr) -> GState -> GState
updateExpr'' g change gst = case (gProof gst,gExpr gst) of
                                  (Just gpr, Just gexpr) -> upd gpr gexpr 
                                  (Nothing, Just gexpr) ->  gst {gExpr = Just gexpr {fExpr = newExpr gexpr}} 
                                  (_,_) -> gst
    where upd gpr gexpr = gst { gProof = Just gpr' }
                -- Para actualizar la expresión dentro de la prueba, asumimos que el foco se encuentra
                -- en la prueba simple que deja a dicha expresión a la derecha.
                where  gpr' = gpr {proof = fromJust $ up (proof gpr) (newExpr gexpr)}
                       up pf f = let up1 = updateEndFocus (goFirstLeft pf) f in
                                    case goRight (fromJust up1) of
                                        Nothing -> Just $ goEnd (fromJust up1)
                                        Just pf' -> Just $ goEnd $ goDownL' $ fromJust $ updateMiddleFocus (goUp' $ fromJust $ updateStartFocus pf' f) f
                       gexpr' = gexpr {fExpr = newExpr gexpr}
                     
          newExpr gexpr = first change . g . goTop . fExpr $ gexpr

updateExpr' :: PreExpr -> Move -> GState -> GState
updateExpr' e p = updateExpr'' p (const e)

    
updateProofNoUndo pf = update (updateProof' pf) >>
                       showProof >>
                       getProof >>= liftIO . debug . show
                       
updateProofWidget pfw = update (\gst -> case gProof gst of
                                             Nothing -> gst
                                             Just gpr -> gst {gProof = Just gpr {
                                                     proofWidget = pfw}
                                             })
    
updateProof pf = update (updateProof' pf) >>
                 showProof >>
                 getProof >>= liftIO . debug . show >>
                 addToUndoList >> restoreValidProofImage

updateProof' :: ProofFocus -> GState -> GState
updateProof' (p,path) gst = case (gProof gst,gExpr gst) of
                              (Just gpr,Just gexpr) -> upd gpr gexpr
                              (_,_) -> gst
    where upd gpr gexpr = gst { gProof = Just gpr { proof = (p,path)
                                                  }
                              , gExpr = Just $ gexpr { fExpr = fromJust $ getEnd p }
                              }
              where pr = proof gpr
                    e = fExpr gexpr
        
-- | Valida la prueba y actualiza el campo "validProof" del ProofState
updateValidProof :: IState ()
updateValidProof = getValidProof >>= \vp -> update (updateValidProof' vp)
    where updateValidProof' :: PM Proof -> GState -> GState
          updateValidProof' vp gst = case gProof gst of
                                       Just gpr -> gst { gProof = Just $ updPrf gpr }
                                       Nothing -> gst
          updPrf gpr = gpr { validProof = validateProof (toProof $ proof gpr) }


updateProofState :: ProofState -> IState ()
updateProofState ps = update (\gst -> gst {gProof = Just ps}) >>
                      addToUndoList >> restoreValidProofImage
                      
unsetProofState :: IState ()
unsetProofState = update (\gst -> gst {gProof = Nothing}) >>
                  addToUndoList >> restoreValidProofImage

updateExprState :: ExprState -> IState ()
updateExprState es = update (\gst -> gst {gExpr = Just es}) >> showExpr

-- | Funcion que actualiza la expresion seleccionada por el usuario al mover el proofFocus.
updateSelectedExpr :: IState ()
updateSelectedExpr = getExprState >>= F.mapM_ 
                       (\es -> getProof >>= \ pf -> 
                              updateExprState (es {fExpr= fromJust $ getEndFocus pf }))

{- Las tres funciones que siguen actualizan componentes particulares
del estado. -}
-- | Pone una nueva expresión en el lugar indicado por la función de ida-vuelta.
updateFocus :: Focus -> GoBack -> IState ()
updateFocus e' f = update (updateFocus' e' f) >> 
                   liftIO (debug "updateFocus") >> 
                   showProof

updateFocus' :: Focus -> GoBack -> GState -> GState
updateFocus' (e,p) (f,g) gst = case gExpr gst of
                                 Just gexpr -> gst { gExpr = Just $ upd gexpr }
                                 Nothing -> gst
    where upd gexpr = gexpr { fExpr = (e,p) }


-- | Actualiza la caja donde tenemos foco de entrada.
updateFrmCtrl :: HBox -> IState ()
updateFrmCtrl l = update (\gst -> case gExpr gst of
                                        Nothing -> gst
                                        Just es -> gst { gExpr = Just $ es {formCtrl = l }})
                                        
                                        
-- | Actualiza el widget de expresión donde tenemos foco de entrada.                                        
updateExprWidget :: ExprWidget -> IState ()
updateExprWidget e = update (\gst -> case gExpr gst of
                                        Nothing -> gst
                                        Just es -> gst { gExpr = Just $ es {exprWidget = e
                                                                           , formCtrl = formBox e
                                                                           }})
            

-- | Actualiza la lista de símbolos para construir expresiones.
updateSymCtrl :: IconView -> IState ()
updateSymCtrl t = update $ \gst -> gst { symCtrl = t }


updateRelation :: Relation -> IState ()
updateRelation r = getProof >>= \(p,path) ->
                   updateProof (updateRel p r,path)
                   
updateAxiomBox :: HBox -> IState ()
updateAxiomBox b = update $ \gst -> gst {gProof = Just $ ((fromJust . gProof) gst) {axiomBox = b}}

addTheorem :: Theorem -> IState Theorem
addTheorem th = (update $ \gst -> gst { theorems = (th:theorems gst) }) >>
                return th

{-changeProofFocus :: (forall ctxTy relTy proofTy exprTy . ProofFocus' ctxTy relTy proofTy exprTy -> 
                    Maybe (ProofFocus' ctxTy relTy proofTy exprTy)) -> 
                    Maybe HBox -> IState ()      -}       
-- changeProofFocus :: (ProofFocus -> Maybe ProofFocus) ->
--                     (ProofFocusWidget -> Maybe ProofFocusWidget) ->
--                     Maybe HBox -> IState ()
-- changeProofFocus moveFocus moveFocusW box = getProof >>=
--                                  updateProofNoUndo . fromJust' . moveFocus >>
--                                  withJust box updateAxiomBox >>
--                                  getProofWidget >>=
--                                  updateProofWidget . fromJust' . moveFocusW
--                                  
--     where fromJust' = maybe (error "MOVIENDO EL FOCUS") id

updateUndoList :: UndoList -> IRG
updateUndoList ulist = update $ \gst -> gst { gUndo = ulist }
                                 
                                 
addToUndoList :: IRG
addToUndoList = getProofState >>= \ps ->
                    case ps of
                         Nothing -> getExprState >>= \es ->
                            F.forM_ es $ \es ->
                                getExpr >>= \e ->
                                addURMove (urmove (Nothing,Just e))
                         Just ps -> getProof >>= \p ->
                                    addURMove (urmove (Just p,Nothing))
                
    where addURMove urm= getUndoing >>= \u -> when u $
                            getProof >>= \p ->
                            getUndoList >>= \ulist ->
                            updateUndoList (urm:ulist) >>
                            getUndoList >>= \ulist' ->
                            liftIO (debug $ "addToUndoList. UndoList es " ++ show ulist') >>
                            cleanRedoList
          urmove (proof,expr) = URMove { urProof = proof
                                       , urExpr = expr}          
             
addToUndoListFromRedo :: URMove -> IRG
addToUndoListFromRedo m = getUndoList >>= \ulist ->
                          updateUndoList (m:ulist)
             
updateRedoList :: RedoList -> IRG
updateRedoList rlist = update $ \gst -> gst { gRedo = rlist }
             
addToRedoList :: URMove -> IRG
addToRedoList m = getRedoList >>= \rlist ->
                  updateRedoList (m:rlist)
                  
updateImageValid :: StockId -> IRG
updateImageValid icon = getStatePart imageValid >>= \validImage ->
                        io (imageSetFromStock validImage icon IconSizeSmallToolbar)
                    

restoreValidProofImage :: IRG
restoreValidProofImage = updateImageValid iconUnknownProof

cleanRedoList :: IRG
cleanRedoList = update $ \gst -> gst { gRedo = [] }

setUndoing :: IRG
setUndoing = update $ \gst -> gst { undoing = True }

setNoUndoing :: IRG
setNoUndoing = update $ \gst -> gst { undoing = False }
 
{- Las nueve funciones siguientes devuelven cada uno de los
componentes del estado. -}

getStatePart :: (GState -> a) -> IState a
getStatePart part = askRef >>= return . part


getStatePartDbg :: String -> (GState -> a) -> IState a
getStatePartDbg msg part = (liftIO $ debug msg) >> getStatePart part

getProof :: IState ProofFocus
getProof = getStatePartDbg "getProof" (proof . fromJust . gProof)

getProofWidget :: IState ProofFocusWidget
getProofWidget = getStatePartDbg "getProofWidget" (proofWidget . fromJust . gProof)

getValidProof :: IState (PM Proof)
getValidProof = getStatePart (maybe (Left errEmptyProof) validProof . gProof)

getProofState :: IState (Maybe ProofState)
getProofState = getStatePartDbg "getProofState" gProof

getExprState :: IState (Maybe ExprState)
getExprState = getStatePartDbg "getExprState" gExpr

getExprProof :: IState Expr
getExprProof = getValidProof >>= either (const (return holeExpr)) (return . getExpr)                    
    where getExpr p = Expr $ BinOp (relToOp (fromJust $ getRel p))
                                   (toExpr $ fromJust $ getStart p)
                                   (toExpr $ fromJust $ getEnd p)
                                     

getRelPF :: IState Relation
getRelPF = getProofState >>= \ps ->
            case ps of
                 Nothing -> return relEq
                 Just ps' -> 
                    getStatePart $ fromJust . getRel . fst . proof . fromJust . gProof


getExpr :: IState Focus
getExpr = getStatePartDbg "getExpr" $ fExpr . fromJust . gExpr

getFocusedExpr :: Move -> IState Focus
getFocusedExpr p = getExpr >>= return . p . goTop

getFrmCtrl :: IState HBox
getFrmCtrl = getStatePartDbg "getFrmCtrl" $ formCtrl . fromJust . gExpr

getExprWidget :: IState ExprWidget
getExprWidget = getStatePartDbg "getExprWidget" $ exprWidget . fromJust . gExpr

getWindow :: IState Window
getWindow = getStatePart gWindow

getTreeExpr :: IState (Maybe TreeExpr)
getTreeExpr = getStatePart gTreeExpr

getFaces :: IState Notebook
getFaces = getStatePart gFaces

getSymCtrl :: IState IconView
getSymCtrl = getStatePartDbg "getSymCtrl" symCtrl

getAxiomCtrl :: IState TreeView
getAxiomCtrl = getStatePartDbg "getAxiomCtrl"  axiomCtrl

getStatus :: IState (Statusbar, ContextId)
getStatus  = getStatePartDbg "getStatus" status

-- getAxiomBox :: IState HBox
-- getAxiomBox = getStatePartDbg "getAxiomBox" $ axiomBox . fromJust . gProof

getStepProofBox :: IState (Maybe HBox)
getStepProofBox = getProofWidget >>= \pfw ->
                  case getBasicFocus pfw of
                       Nothing -> return Nothing
                       Just b -> return (Just $ stepBox b)


getAxiomBox :: IState HBox
getAxiomBox = getProofWidget >>= \pfw ->
              return (axiomWidget $ fromJust $ getBasicFocus pfw)

getAxiomBox' :: IState (Maybe HBox)
getAxiomBox' = getStatePartDbg "getAxiomBox" $ \s -> gProof s >>= (return . axiomBox)

{- Las dos funciones que siguen devuelven cada uno de los panes; toda la 
   gracia está en getParentNamed. -}

-- | Retorna la caja contenedora de los widget de operadores de pre-expresion.
getTreeOpBox :: IState VBox
getTreeOpBox = getFaces >>= \f -> liftIO (notebookGetNthPage f 1) >>= 
                 \(Just w) -> liftIO (containerGetChildren (castToBox w)) >>= 
                 \[_,w'] -> liftIO (containerGetChildren (castToBox w')) >>= 
                 \[_,m,_,_,_] -> liftIO (containerGetChildren (castToContainer m)) >>= 
                 \[m',_] -> return $ castToVBox m'

-- | Retorna la caja contenedora de los widget de variables de cuantificador
--  de pre-expresion.
getTreeVarQBox :: IState VBox
getTreeVarQBox = getFaces >>= \f -> liftIO (notebookGetNthPage f 1) >>= 
                 \(Just w) -> liftIO (containerGetChildren (castToBox w)) >>= 
                 \[_,w'] -> liftIO (containerGetChildren (castToBox w')) >>= 
                 \[_,_,m,_,_] -> liftIO (containerGetChildren (castToContainer m)) >>= 
                 \[m',_] -> return $ castToVBox m'

getTreeQuantBox :: IState VBox
getTreeQuantBox = getFaces >>= \f -> liftIO (notebookGetNthPage f 1) >>= 
                 \(Just w) -> liftIO (containerGetChildren (castToBox w)) >>= 
                 \[_,w'] -> liftIO (containerGetChildren (castToBox w')) >>= 
                 \[_,_,_,m,_] -> liftIO (containerGetChildren (castToContainer m)) >>= 
                 \[m',_] -> return $ castToVBox m'

-- | Retorna la caja contenedora del árbol de tipado de una pre-expresion.
getTreeExprBox :: IState VBox
getTreeExprBox = getFaces >>= \f -> liftIO (notebookGetNthPage f 1) >>= 
                 \(Just w) -> liftIO (containerGetChildren (castToBox w)) >>= 
                 \[_,w'] -> liftIO (containerGetChildren (castToBox w')) >>= 
                 \[_,_,_,_,m] -> return $ castToVBox m

-- | Devuelve el paned que contiene la lista de símbolos.
getSymFrame :: IState Frame
getSymFrame = getSymCtrl >>= getParentNamed "symFrame". toWidget >>=
              return . castToFrame

getAxiomFrame :: IState Frame
getAxiomFrame = getAxiomCtrl >>= getParentNamed "axiomFrame" . toWidget >>=
                return . castToFrame

-- | Devuelve el paned que contiene al widget de fórmulas.
getFormPane :: IState Paned
getFormPane = getFrmCtrl >>=
              getParentNamed "formPane" . toWidget >>=
              return . castToPaned

-- | Devuelve el paned que contiene al widget de errores.
-- TODO: Queda muy fea la parte de la lista con tres elementos.
getErrPane :: IState Paned
getErrPane = getSymFrame >>= liftIO . widgetGetParent >>= \(Just w) ->
             liftIO (containerGetChildren (castToContainer w)) >>= \[_,m,_] ->
             return $ castToPaned m

-- | Devuelve el label que reporta los errores.
getErrPanedLabel :: IState EventBox
getErrPanedLabel = getErrPane >>= \erp -> liftIO (panedGetChild1 erp) >>= 
                   \(Just eb) -> return $ castToEventBox eb

-- | Devuelve el ancestro que tiene un nombre. ¡Es insegura!
getParentNamed :: String -> Widget -> IState Widget
getParentNamed name = go
    where go w = liftIO (G.get w widgetName) >>= \name' ->
                 liftIO (debug (maybe "Sin nombre" (\n -> if null n then "Nombre vacio" else n) name')) >>
                 if maybe False (== name) name'
                 then return w
                 else liftIO (widgetGetParent w) >>= go . fromJust

getTheorems :: IState [Theorem]
getTheorems = getStatePart theorems
        
        
getUndoList :: IState UndoList
getUndoList = getStatePart gUndo

getRedoList :: IState RedoList
getRedoList = getStatePart gRedo
 
getUndoing :: IState Bool
getUndoing = getStatePart undoing

-- -- | Devuelve la expresión que está enfocada en un momento dado.
getSelectedExpr :: IState Focus
getSelectedExpr = getProof >>= return . fromJust . getEndFocus
 
-- TODO: debemos hacer renombre si la variable está ligada?
-- | Actualización de la variable de cuantificación.
--updateQVar :: String -> IState ()
updateQVar v p = update (updateExpr'' id putVar) 
    where putVar (Quant q _ r t) = Quant q v r t
          putVar e = e

selectExprFromBox :: HBox -> IState ()
selectExprFromBox = selectFrom (formCtrl)

selectTypeFromBox :: HBox -> IState ()
selectTypeFromBox = selectFrom (eventType)

selectFrom :: (ExprState -> HBox) -> HBox -> IState ()
selectFrom eventTE eb = getTreeExpr >>= \(Just tExpr) ->
                case ( eventTE (mainExpr tExpr) == eb
                     , find (\te -> (eventTE te) == eb) (atomExpr tExpr)
                     , find (\te -> (eventTE te) == eb) (quantExpr tExpr)
                     )
                of
                    (True,_,_) -> update (\gst -> gst {gExpr = Just $ mainExpr tExpr})
                    (_,Just se,_) -> update (\gst -> gst {gExpr = Just se })
                    (_,_,Just se) -> update (\gst -> gst {gExpr = Just se })
                    _ -> return ()

searchFocusInTree :: Focus -> IState [ExprState]
searchFocusInTree f = getTreeExpr >>= \(Just tExpr) ->
                case ( fExpr (mainExpr tExpr) == f
                     , filter (\te -> (fExpr te) == f) (atomExpr tExpr)
                     )
                of
                    (False, []) -> return ([mainExpr tExpr])
                    (True,_) -> return $ [mainExpr tExpr]
                    (_,ses) -> return $ ses

updateTypeQuantInExprTree :: ExprState -> Type -> IState ()
updateTypeQuantInExprTree es t = 
                        getTreeExpr >>= \(Just tExpr) ->
                        getQuantExprTree >>= \qETree ->
                        update (\gst -> gst {gTreeExpr = Just $
                                                tExpr {quantExpr = qETree' qETree} 
                                            })
    where qETree' :: [ExprState] -> [ExprState]
          qETree' les = map (\te -> if (eventType te) == (eventType es) 
                                        then te {fType = t}
                                        else te ) les

updateTypeAtomInExprTree :: ExprState -> Type -> IState ()
updateTypeAtomInExprTree es t = 
                        getTreeExpr >>= \(Just tExpr) ->
                        getAtomExprTree >>= \aETree ->
                        update (\gst -> gst {gTreeExpr = Just $
                                                tExpr {atomExpr = aETree' aETree} 
                                            })
    where aETree' :: [ExprState] -> [ExprState]
          aETree' les = map (\te -> if (eventType te) == (eventType es) 
                                        then te {fType = t}
                                        else te ) les

-- | Actualiza el tipo de un operador en la expresión principal del árbol de
-- tipado, en base a una lista de focus y moves.
updateTypeOpInMainExprTree :: [(Focus, Move)] -> Type -> IState ()
updateTypeOpInMainExprTree fs t = getMainExprTree >>= \exprT ->
                                  updateMainExprTree exprT {fExpr = (setType fs t (fExpr exprT))}

updateTypeQuantInMainExprTree :: ExprState -> Type -> IState ()
updateTypeQuantInMainExprTree es qt = getMainExprTree >>= \exprT ->
                                      updateMainExprTree exprT 
                                                {fExpr = setQuantType 
                                                            (fExpr exprT) id
                                                            qt}

updateTypeVarQInMainExprTree :: ExprState -> Type -> IState ()
updateTypeVarQInMainExprTree es qt = getMainExprTree >>= \exprT ->
                                      updateMainExprTree exprT 
                                                {fExpr = setVarQType 
                                                            (fExpr exprT) id
                                                            qt}


-- | Actualiza el tipo de un atomo en la expresión principal del árbol de
-- tipado, en base a un exprState.
updateTypeAtomInMainExprTree :: ExprState -> Type -> IState ()
updateTypeAtomInMainExprTree es t = getMainExprTree >>= \exprT ->
                                    updateMainExprTree exprT 
                                                {fExpr = setAtomType (fExpr exprT) id t}

updateExprSelectExpr :: ExprState -> PreExpr -> IState ()
updateExprSelectExpr es e = update (\gst -> gst {gExpr = Just es'})
    where
        es' :: ExprState
        es' = es {fExpr = (toFocus . toExpr . (flip replace $ e) . fExpr) es}

updateTypeSelectType :: ExprState -> Type -> IState ()
updateTypeSelectType es t = update (\gst -> gst {gExpr = Just es'})
    where
        es' :: ExprState
        es' = es {fType = t}

updateMainExprTree :: ExprState -> IState ()
updateMainExprTree es = updateMTT $ return . tExpr
    where tExpr :: (Maybe TreeExpr) -> TreeExpr
          tExpr Nothing = TreeExpr es [] [] []
          tExpr (Just te) = TreeExpr es (opExpr te) (atomExpr te) (quantExpr te)

updateOpExprTree :: [[(Focus, Move)]] -> (Maybe [(Focus,Move)]) -> (Maybe Type) -> IState ()
updateOpExprTree fss Nothing Nothing = updateMTT $ return . tExpr
    where tExpr :: (Maybe TreeExpr) -> TreeExpr
          tExpr (Just te) = TreeExpr (mainExpr te) 
                                     fss 
                                     (atomExpr te)
                                     (quantExpr te)
updateOpExprTree fss (Just fs) (Just t) = (update (\gst -> gst {gTreeExpr = Just $ tExpr (gTreeExpr gst)}))
    where 
          fss' = deleteBy (\fs' -> \fs -> ((fst . unzip) fs') == ((fst . unzip) fs)) fs fss
          tExpr :: (Maybe TreeExpr) -> TreeExpr
          tExpr (Just te) = TreeExpr (mainExpr te) 
                                     fss 
                                     (atomExpr te)
                                     (quantExpr te)

-- | Limpia el árbol de tipado del estado general.
cleanTreeExpr :: IState ()
cleanTreeExpr = updateMTT (const Nothing) >> 
                getExprState >>= \(Just es) -> 
                updateTypeSelectType es TyUnknown


-- Añade una expresion y su respectivo boton a al arbol de tipado.
-- addMainExprToTree :: Focus -> Type -> GoBack -> HBox -> HBox -> IState ExprState
-- addMainExprToTree f t p be bt = updateTT (\gte -> gte { mainExpr = te }) >>
--                                 return te
--     where te :: ExprState
--           te = ExprState { fExpr = f
--                          , fType = t
--                          , pathExpr = p
--                          , eventExpr = be
--                          , eventType = bt
--                          }
                         
-- Funcion que chequea si la prueba en la interfaz está validada
checkValidProof :: IState Bool
checkValidProof = getProof >>= \pf ->
                  return (toProof pf) >>= \pr ->
                  liftIO (debug ("la prueba es " ++ show pr)) >>
                  getValidProof >>= \vp ->
                  liftIO (debug ("la prueba valida es " ++ show vp))  >>
                  case vp of
                       Left _ -> return False
                       Right p -> return (p==pr)

-- | 
updateTT :: (TreeExpr -> TreeExpr) -> IState ()
updateTT f = askRef >>= \gst -> 
             case gTreeExpr gst of
               Just gte -> update $ \gst -> gst { gTreeExpr = return $ f gte }
               _ -> return ()

updateMTT :: (Maybe TreeExpr -> Maybe TreeExpr) -> IState ()
updateMTT f = askRef >>= \gst -> update $ \gst -> gst { gTreeExpr = f (gTreeExpr gst) }


-- | Actualiza el tipo de la expresión principal del árbol de tipado.
updateMainExprTreeType :: Type -> IState ()
updateMainExprTreeType t = getMainExprTree >>= \eTree ->
                           updateTT $ \gte -> gte {mainExpr = te eTree t }
    where te :: ExprState -> Type ->  ExprState
          te es t = es { fType = t }

-- | Añade un exprState a la lista de atomos del árbol de tipado.
addAtomExprTree :: ExprState -> IState ()
addAtomExprTree es = getAtomExprTree >>= \l ->
                     updateTT $ \gte -> gte {atomExpr = es:l}

-- | Añade un exprState a la lista de cuantificadores del árbol de tipado.
addQuantExprTree :: ExprState -> IState ()
addQuantExprTree es =  getQuantExprTree >>= \l ->
                       updateTT $ \gte -> gte {quantExpr = es:l}

getMainExprTree :: IState ExprState
getMainExprTree = getStatePartDbg "getMainExprTree" 
                                            (mainExpr . fromJust . gTreeExpr)

getOpExprTree :: IState [[(Focus, Move)]]
getOpExprTree = askRef >>= return . opExpr . fromJust . gTreeExpr

getAtomExprTree :: IState [ExprState]
getAtomExprTree = askRef >>= return . atomExpr . fromJust . gTreeExpr

getQuantExprTree :: IState [ExprState]
getQuantExprTree = askRef >>= return . quantExpr . fromJust . gTreeExpr


-- | Ejecuta una acción en la mónada de estado para obtener un
-- resultado. Es útil para los event-handlers.
withState :: (IO a -> IO b) -> IState a -> IState b
withState f m = get >>= liftIO . f . evalStateT m

eventWithState :: IState a -> GRef -> EventM t a
eventWithState m = liftIO . evalStateT m

-- | Estado inicial
initialState :: Window -> IconView -> TreeView -> Notebook -> Statusbar -> ContextId -> Image -> GState
initialState win sl al fc sb ce valid = GState 
                                    win
                                    Nothing
                                    Nothing
                                    Nothing
                                    sl
                                    al
                                    fc
                                    []
                                    []
                                    (Statistic [])
                                    (sb,ce)
                                    [] -- lista de teoremas, TODO: que se carguen los teoremas desde disco
                                    beginCtx -- Contexto de hipótesis.
                                    True -- undoing
                                    valid -- image

-- Funciones para manipular y obtener la lista de hipótesis
getGlobalCtx :: IState Ctx
getGlobalCtx = getStatePart hypothesis

-- | Intenta agregar una hipotesis al contexto global.
addGlobalHypothesis :: PreExpr -> IState (Maybe Name)
addGlobalHypothesis e = askRef >>= addHyp
    where addHyp st = case addBoolHypothesis e (hypothesis st) of
                        (ctx,Nothing) -> return Nothing
                        (ctx',Just n) -> update (\st -> st { hypothesis = ctx' }) >> (return $ Just n)

getGlobalHypothesis :: Name -> IState (Maybe Hypothesis)
getGlobalHypothesis n = getGlobalCtx >>= return . getHypothesis n