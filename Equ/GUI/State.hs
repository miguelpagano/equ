{-# Language OverloadedStrings , RankNTypes #-}
-- | Utilidades varias que tienen que ver con el estado de la
-- interfaz (es probable que se muden a Equ.GUI.State) y con
-- funciones convenientes que podrían mudarse a otros módulos.
module Equ.GUI.State ( -- * Proyeccion de componentes del estado
                       module Equ.GUI.State.Expr
                     , module Equ.GUI.State.Proof
                     , module Equ.GUI.State.Undo
                     , getSymFrame
                     , getParentNamed
                     , getWindow
                     , getAxiomFrame
                     , getErrPane
                     , getErrPanedLabel
                     , eventWithState
                     , getSymCtrl
                     , getSymStore
                     , getSymCid
                     , updateSymCid
                     , getAxiomCtrl
                     , getAxiomBox
                     , getAxiomBox'
                     , getExprProof
                     , getStepProofBox
                     -- * Modificacion del estado.
                     , updateExpr
                     , updateFocus
                     , updateProofUndo
                     , updateProofNoUndo
                     -- * Otras funciones
                     , withState
                     , checkValidProof
                     , initialState
                     -- * Funciones relacionadas con arbol de tipos
                     , module Equ.GUI.State.TypeTree
                     -- * Funciones relacionadas con pruebas
                     , updateProofState 
                     , unsetProofState
                     , changeProofFocus
                     , module Equ.GUI.State.Internal
                     -- * Manipulación del contexto global
                     , module Equ.GUI.State.Ctx
                     )
    where

import Equ.GUI.State.Internal
import Equ.GUI.State.Expr
import Equ.GUI.State.Proof 
import Equ.GUI.State.Ctx
import Equ.GUI.State.SymbolList
import Equ.GUI.State.Undo
import Equ.GUI.State.TypeTree
import Equ.GUI.Types
import Equ.GUI.Utils

import Equ.PreExpr (Focus,PreExpr)

import Equ.Theories (getExprProof)

import Equ.Proof.Proof
import Equ.Proof.Error(errEmptyProof)
import Equ.Proof(ProofFocus,ProofFocus',updateStartFocus,updateEndFocus,PM,validateProof,
                 toProof,goFirstLeft,updateMiddleFocus,goUp',getEndFocus,goRight,goEnd,goDownL',
                  getBasicFocus, validateProofFocus, goNextStep, goPrevStep)
import Equ.Exercise (Exercise)


import Graphics.UI.Gtk hiding (eventButton, eventSent, get)
import qualified Graphics.UI.Gtk as G

import Control.Arrow(first,(&&&))
import Data.Maybe(fromJust)

import qualified Data.Foldable as F (mapM_,forM_) 

-- | Pone una nueva expresión en el lugar indicado por la función de ida-vuelta.
updateExpr :: PreExpr -> Move -> IState ()
updateExpr e' p = update (updateExpr' e' p) >> 
                  showExpr >> 
                  addToUndoList >> 
                  restoreValidProofImage >>
                  -- validamos el paso en el que esta la expresion y el siguiente, si lo tiene
                  validateStep >> 
                  changeProofFocus (Just . goNextStep) (Just . goNextStep) Nothing >> 
                  validateStep >> 
                  changeProofFocus (Just . goPrevStep) (Just . goPrevStep) Nothing

updateExpr' :: PreExpr -> Move -> GState -> GState
updateExpr' e p = updateExpr'' p (const e)

-- | Pone una nueva expresión en el lugar indicado por la función de ida-vuelta.
updateFocus :: Focus -> GoBack -> IState ()
updateFocus e' f = update (updateFocus' e' f) >> 
                   io (debug "updateFocus") >> 
                   showProof

-- | Actualización de la prueba, agregando la posibilidad de deshacer.
updateProofUndo :: ProofFocus -> IState ()
updateProofUndo pf = updateProof pf >>
                     showProof >>
                     getProof >>= io . debug . show >>
                     addToUndoList >> restoreValidProofImage

-- | Actualización de la prueba, sin deshacer.    
updateProofNoUndo pf = updateProof pf >>
                       showProof >>
                       getProof >>= io . debug . show                                 

updateProofState :: ProofState -> IState ()
updateProofState ps = update (\gst -> gst {gProof = Just ps}) >>
                      addToUndoList >> 
                      restoreValidProofImage

-- | Descarta la prueba actual.    
unsetProofState :: IState ()
unsetProofState = update (\gst -> gst {gProof = Nothing}) >>
                  addToUndoList >> 
                  restoreValidProofImage



changeProofFocus :: (ProofFocus -> Maybe ProofFocus) ->
                   (ProofFocusWidget -> Maybe ProofFocusWidget) ->
                   Maybe HBox -> IState ()
changeProofFocus moveFocus moveFocusW box = getProofState >>=
                                            F.mapM_ (\_ ->
                                                     getProof >>=
                                                     updateProofNoUndo . fromJust' . moveFocus >>
                                                     withJust box updateAxiomBox >>
                                                     getProofWidget >>=
                                                     updateProofWidget . fromJust' . moveFocusW
                                                    )
--                                  
    where fromJust' = maybe (error "MOVIENDO EL FOCUS") id

getWindow :: IState Window
getWindow = getStatePart gWindow

getAxiomCtrl :: IState TreeView
getAxiomCtrl = getStatePartDbg "getAxiomCtrl"  axiomCtrl

getStatus :: IState (Statusbar, ContextId)
getStatus  = getStatePartDbg "getStatus" status

getStepProofBox :: IState (Maybe HBox)
getStepProofBox = getProofWidget >>= \pfw ->
                  case getBasicFocus pfw of
                       Nothing -> return Nothing
                       Just b -> return (Just $ stepBox b)

getAxiomBox :: IState HBox
getAxiomBox = getProofWidget >>= \pfw ->
              return (axiomWidget $ fromJust $ getBasicFocus pfw)

getAxiomBox' :: IState (Maybe HBox)
getAxiomBox' = getProofState >>= \ps ->
               case ps of
                    Nothing -> return Nothing
                    Just s -> getAxiomBox >>= return . Just

-- | Devuelve el paned que contiene la lista de símbolos.
getSymFrame :: IState Frame
getSymFrame = getSymCtrl >>= getParentNamed "symFrame". toWidget >>=
              return . castToFrame

getAxiomFrame :: IState Frame
getAxiomFrame = getAxiomCtrl >>= getParentNamed "axiomFrame" . toWidget >>=
                return . castToFrame

-- | Devuelve el paned que contiene al widget de errores.
-- TODO: Queda muy fea la parte de la lista con tres elementos.
getErrPane :: IState Paned
getErrPane = getSymFrame >>= io . widgetGetParent >>= \(Just w) ->
             io (containerGetChildren (castToContainer w)) >>= \[_,m,_] ->
             return $ castToPaned m

-- | Devuelve el label que reporta los errores.
getErrPanedLabel :: IState EventBox
getErrPanedLabel = getErrPane >>= \erp -> io (panedGetChild1 erp) >>= 
                   \(Just eb) -> return $ castToEventBox eb

-- | Devuelve el ancestro que tiene un nombre. ¡Es insegura!
getParentNamed :: String -> Widget -> IState Widget
getParentNamed name = go
    where go w = io (G.get w widgetName) >>= \name' ->
                 io (debug (maybe "Sin nombre" (\n -> if null n then "Nombre vacio" else n) name')) >>
                 if maybe False (== name) name'
                 then return w
                 else io (widgetGetParent w) >>= go . fromJust

                         
-- Funcion que chequea si la prueba en la interfaz está validada
checkValidProof :: IState Bool
checkValidProof = getProof >>= \pf ->
                  return (toProof pf) >>= \pr ->
                  io (debug ("la prueba es " ++ show pr)) >>
                  getValidProof >>= \vp ->
                  io (debug ("la prueba valida es " ++ show vp))  >>
                  case vp of
                       Left _ -> return False
                       Right p -> return (p==pr)

-- | Ejecuta una acción en la mónada de estado para obtener un
-- resultado. Es útil para los event-handlers.
withState :: (IO a -> IO b) -> IState a -> IState b
withState f m = get >>= io . f . evalStateT m

eventWithState :: IState a -> GRef -> EventM t a
eventWithState m = io . evalStateT m

-- | Estado inicial
initialState :: Window -> IconView -> ListStore SynItem -> 
               TreeView -> Maybe Exercise -> Statusbar -> ContextId -> Image -> GState
initialState win sl ss al me sb ce valid = GState 
                                    win
                                    Nothing
                                    Nothing
                                    Nothing
                                    sl
                                    ss
                                    Nothing
                                    al
                                    me
                                    []
                                    []
                                    (sb,ce)
                                    [] -- lista de teoremas, TODO: que se carguen los teoremas desde disco
                                    beginCtx -- Contexto de hipótesis.
                                    True -- undoing
                                    valid -- image

