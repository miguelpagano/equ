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
                     , getStepProofBox
                     , getSelIndexProof
                     -- * Modificacion del estado.
                     , updateExpr
                     , updateRelation
                     , updateFocus
                     , updateProofUndo
                     , updateProofNoUndo
                     -- * Otras funciones
                     , withState
                     , checkValidProof
                     , validateStep
                     , initialState
                     -- * Funciones relacionadas con arbol de tipos
                     , module Equ.GUI.State.TypeTree
                     -- * Funciones relacionadas con pruebas
                     , updateProofState 
                     , unsetExprState
                     , unsetProofState
                     , changeProofFocus
                     , module Equ.GUI.State.Internal
                     -- * Manipulación del contexto global
                     , module Equ.GUI.State.Ctx
                     )
    where

import Equ.GUI.State.Internal
import Equ.GUI.State.Expr
import Equ.GUI.State.Proof hiding (validateStep)
import qualified Equ.GUI.State.Proof as Proof
import Equ.GUI.State.Ctx
import Equ.GUI.State.SymbolList
import Equ.GUI.State.Undo
import Equ.GUI.State.TypeTree
import Equ.GUI.Types
import Equ.GUI.Utils
import Equ.GUI.Settings

import Equ.PreExpr (Focus,PreExpr,PreExpr'(BinOp),toExpr)
import Equ.Expr
import Equ.Syntax
import Equ.Theories (getExprProof,relToOp)

import Equ.Exercise(Exercise)

import Equ.Proof.Proof
import Equ.Proof.Error(errEmptyProof)
import Equ.Proof(ProofFocus,ProofFocus',ProofFocusAnnots,updateStartFocus,updateEndFocus,PM,validateProof,
                 toProof,goFirstLeft,updateMiddleFocus,goUp',getEndFocus,goRight,goEnd,goDownL',
                  getBasicFocus, validateListedProof,validateStepProof, goNextStep, goPrevStep)
import Equ.Proof.ListedProof
import Equ.Rule

import Graphics.UI.Gtk hiding (eventButton, eventSent, get)
import qualified Graphics.UI.Gtk as G

import Control.Arrow(first,(&&&))
import Data.Maybe(fromJust)

import qualified Data.Foldable as F (mapM_,forM_)

-- | ValidateStep + marcado de la expresión re-escrita.
validateStep :: IState ()
validateStep = Proof.validateStep (\p ->
                    getProofWidget >>= \lpw ->
                    return (getStartExpr lpw) >>= \sew ->
                    findPathBox (fromJust $ getStart p) sew >>= \focusBox ->
                    if getFocusBox sew /= (Just focusBox) then
                        unmarkedExprBox sew >>
                        markupExprBox focusBox >>
                        updateFocusBoxExprWidget (ctw focusBox) sew
                    else
                        return ())
    where
        containerRemoveChildren :: ContainerClass c => c -> IO ()
        containerRemoveChildren c = (containerForeach c) 
                                        (\w -> containerRemove c w)
        getChildren :: WidgetClass w => w -> IO [Widget] 
        getChildren w = containerGetChildren (castToBox w) >>= \ws ->
                        containerRemoveChildren (castToBox w) >>
                        return ws
        makeMarkup :: BoxClass b => b -> IO ()
        makeMarkup b = hSeparatorNew >>= \sep -> 
                       widgetModifyBg sep (toEnum 0) underlineBg >>
                       boxPackEnd b sep PackNatural 0
        fillBox :: BoxClass b => b -> [Widget] -> IO ()
        fillBox b = mapM_ (\w -> boxPackStart b w PackNatural 3)
        markupExprBox :: WidgetClass w => w -> IState () 
        markupExprBox w = let focusBox = castToBox w in
                            io $ do
                            vBox <- vBoxNew False 0
                            focusBoxNew <- hBoxNew False 0
                            ws <- getChildren focusBox
                            fillBox focusBoxNew ws
                            makeMarkup vBox
                            boxPackEnd vBox focusBoxNew PackNatural 4
                            boxPackEnd focusBox vBox PackNatural 3
                            widgetShowAll focusBox
        unmarkedExprBox :: ExprWidget -> IState ()
        unmarkedExprBox ew = io $ 
                case getFocusBox ew of
                    Nothing -> return ()
                    Just fBox -> 
                            let actualFocusBox = castToBox fBox in
                                io $ do
                                [vBox] <- getChildren actualFocusBox
                                [hBox, sepBox] <- getChildren (castToBox vBox)
                                boxs <- getChildren $ hBox
                                fillBox actualFocusBox boxs

-- | Pone una nueva expresión en el lugar indicado por la función de ida-vuelta.
updateExpr :: PreExpr -> Move -> IState ()
updateExpr e' p = Proof.getProofState >>= \ps ->
                  case ps of
                       Nothing -> upd e' p
                       Just ps' -> debuging >> upd e' p
                
    where upd e' p = update (updateExpr' e' p) >> 
                     showExpr >> 
                     addToUndoList >> 
                     Proof.restoreValidProofImage >>
                     -- validamos el paso en el que esta la expresion y el siguiente, si lo tiene
                     validateStep >> 
                     Proof.getProofState >>=
                     F.mapM_ (\ps -> Proof.getProof >>= return . isLastSelected >>= \b ->
                     if not b 
                        then moveNextProofStep >> validateStep >> movePrevProofStep
                        else return ()
                     )  
          debuging = Proof.getProof >>=
                  return . selIndex >>= \ip ->
                  Proof.getProofWidget >>=
                  return . selIndex >>= \ipw ->
                  io (debug $ "updating Expr, indice seleccionado: Proof = " ++ (show ip) ++
                            " ProofWidget = " ++ (show ipw))

-- | Pone una nueva expresión en el lugar indicado por la función de ida-vuelta.
updateFocus :: Focus -> GoBack -> IState ()
updateFocus e' f = update (updateFocus' e' f) >> 
                   io (debug "updateFocus") >> 
                   Proof.showProof

-- | Actualización de la prueba, agregando la posibilidad de deshacer.
updateProofUndo :: ListedProof -> IState ()
updateProofUndo lp = update (Proof.updateProof' lp) >>
                 Proof.showProof >>
                 Proof.getProof >>= io . debug . show >>
                 addToUndoList >> Proof.restoreValidProofImage

updateProofNoUndo pf = update (Proof.updateProof' pf) >>
                       Proof.showProof >>
                       Proof.getProof >>= io . debug . show

updateProofState :: ProofState -> IState ()
updateProofState ps = update (\gst -> gst {gProof = Just ps}) >>
                      addToUndoList >> 
                      Proof.restoreValidProofImage
                      
unsetExprState :: IState ()
unsetExprState = update (\gst -> gst {gExpr = Nothing})

-- | Descarta la prueba actual.    
unsetProofState :: IState ()
unsetProofState = update (\gst -> gst {gProof = Nothing}) >>
                  addToUndoList >> 
                  Proof.restoreValidProofImage

-- | Actualiza la caja donde tenemos foco de entrada.
updateFrmCtrl :: HBox -> IState ()
updateFrmCtrl l = update (\gst -> case gExpr gst of
                                        Nothing -> gst
                                        Just es -> gst { gExpr = Just $ es {formCtrl = l }})

-- | Actualiza la lista de símbolos para construir expresiones.
updateSymCtrl :: IconView -> IState ()
updateSymCtrl t = update $ \gst -> gst { symCtrl = t }


updateRelation :: Relation -> IState ()
updateRelation r = Proof.getProof >>= \lp ->
                   updateProofUndo $ updateRelLP lp r

addTheorem :: Theorem -> IState Theorem
addTheorem th = (update $ \gst -> gst { theorems = (th:theorems gst) }) >>
                return th

changeProofFocus :: Int -> IState ()
changeProofFocus i = Proof.getProofState >>=
                     F.mapM_ (\ps ->
                        io (debug "\n---changeProofFocus---") >>
                        Proof.getProof >>= \lp ->
                        updateProofNoUndo (moveToPosition i lp) >>
                        Proof.getProofWidget >>= \lpw ->
                        Proof.updateProofWidget (moveToPosition i lpw) >>
                        Proof.getProofWidget >>= \lpw' ->
                        return (getSelExpr lpw') >>= \ew ->
                        io (debug $ "Ewidget seleccionado es: "++show ew) >>
                        Proof.showProof
                        )
                        
moveNextProofStep :: IState ()
moveNextProofStep = Proof.getProofState >>=
                    F.mapM_ (\ps ->
                        Proof.getProof >>= \lp ->
                        updateProofNoUndo (moveToNextPosition lp) >>
                        Proof.getProofWidget >>= \lpw ->
                        Proof.updateProofWidget (moveToNextPosition lpw)
                        )

movePrevProofStep :: IState ()
movePrevProofStep = Proof.getProofState >>=
                    F.mapM_ (\ps ->
                        Proof.getProof >>= \lp ->
                        updateProofNoUndo (moveToPrevPosition lp) >>
                        Proof.getProofWidget >>= \lpw ->
                        Proof.updateProofWidget (moveToPrevPosition lpw)  
                        )

getExprProof :: IState Expr
getExprProof = Proof.getValidProof >>= either (const (return holeExpr)) (return . getExpr)                    
    where getExpr p = Expr $ BinOp (relToOp (fromJust $ getRel p))
                                   (toExpr $ fromJust $ getStart p)
                                   (toExpr $ fromJust $ getEnd p)
                             
getSelIndexProof :: IState Int
getSelIndexProof = Proof.getProofState >>= \ps ->
                   case ps of
                        Nothing -> return 0
                        Just ps' -> Proof.getProof >>= return . selIndex

getWindow :: IState Window
getWindow = getStatePart gWindow

getAxiomCtrl :: IState TreeView
getAxiomCtrl = getStatePartDbg "getAxiomCtrl"  axiomCtrl

getStatus :: IState (Statusbar, ContextId)
getStatus  = getStatePartDbg "getStatus" status

getStepProofBox :: IState (Maybe HBox)
getStepProofBox = Proof.getProofWidget >>= \lpw ->
                  case getSelBasic lpw of
                       Nothing -> return Nothing
                       Just b -> return (Just $ stepBox b)

getAxiomBox :: IState HBox
getAxiomBox = Proof.getProofWidget >>= \lpw ->
              return (axiomWidget $ fromJust $ getSelBasic lpw)

getAxiomBox' :: IState (Maybe HBox)
getAxiomBox' = Proof.getProofState >>= \ps ->
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
             io (containerGetChildren (castToContainer w)) >>= \[m,_] ->
             return $ castToPaned m

-- | Devuelve el label que reporta los errores.
getErrPanedLabel :: IState EventBox
getErrPanedLabel = getErrPane >>= \erp -> io (panedGetChild1 erp) >>= 
                   \(Just eb) -> return $ castToEventBox eb

-- | Devuelve el ancestro que tiene un nombre. ¡Es insegura!
getParentNamed :: String -> Widget -> IState Widget
getParentNamed name = go
    where go w = io (G.get w widgetName) >>= \name' ->
                 io (debug 
                 (maybe "Sin nombre" 
                 (\n -> if null n then "Nombre vacio" else n) name')) >>
                 if maybe False (== name) name'
                 then return w
                 else io (widgetGetParent w) >>= go . fromJust

                         
-- Funcion que chequea si la prueba en la interfaz está validada
checkValidProof :: IState Bool
checkValidProof = Proof.getProof >>= \lp ->
                  return (toProof (pFocus lp)) >>= \pr ->
                  io (debug ("la prueba es " ++ show pr)) >>
                  Proof.getValidProof >>= \vp ->
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

