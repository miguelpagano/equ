-- | Interfaz gráfica de Equ.
module Equ.GUI.Gui where

import Equ.GUI.Exercise
import Equ.GUI.Types
import Equ.GUI.State
import Equ.GUI.Utils
import Equ.GUI.Widget
import Equ.GUI.Settings
import Equ.GUI.Expr
import Equ.GUI.SymbolList
import Equ.GUI.TruthList
import Equ.GUI.Proof 
import Equ.GUI.TypeTree
import Equ.GUI.Truth
import Equ.GUI.Undo
import Equ.GUI.Proof.Dialogs

import Equ.PreExpr(holePreExpr, emptyExpr)

import qualified Graphics.UI.Gtk as G
import Graphics.UI.Gtk hiding (eventButton, eventSent,get)
import Graphics.UI.Gtk.Gdk.Events 
import Graphics.UI.Gtk.Glade
import Data.Text (pack,unpack)

import Data.Reference

import Control.Monad(liftM, when)
import Control.Monad.Reader

import qualified Data.Foldable as F (forM_)

import Data.Map (fromList)

main :: IO ()
main = do 
    initGUI

    -- TODO: qué pasa si no existe el archivo.
    Just xml <- xmlNew "Equ/GUI/equ.glade"

    -- get widgets
    window        <- xmlGetWidget xml castToWindow "mainWindow"
    quitButton    <- getMenuButton xml "QuitButton"

    statusBar     <- xmlGetWidget xml castToStatusbar "statusBar"
    ctxExpr       <- statusbarGetContextId statusBar "Expr"
    symbolList    <- xmlGetWidget xml castToIconView "symbolList"
    axiomList     <- xmlGetWidget xml castToTreeView "axiomList"
    
    symFrame <- xmlGetWidget xml castToFrame "symFrame"
    axiomFrame <- xmlGetWidget xml castToFrame "axiomFrame"
    errPane <- xmlGetWidget xml castToPaned "errPane"

    centralBox <- xmlGetWidget xml castToVBox "centralBox"


    itemNewProof <- xmlGetWidget xml castToImageMenuItem "itemNewProof"
    itemLoadProof <- xmlGetWidget xml castToImageMenuItem "itemLoadProof"
    itemSaveProof <- xmlGetWidget xml castToImageMenuItem "itemSaveProof"
    itemDiscardProof <- xmlGetWidget xml castToImageMenuItem "itemDiscardProof"
    itemSaveAsTheorem <- xmlGetWidget xml castToImageMenuItem "itemSaveAsTheorem"
    
    itemUndo <- xmlGetWidget xml castToImageMenuItem "undoMenuItem"
    itemRedo <- xmlGetWidget xml castToImageMenuItem "redoMenuItem"
    
    itemMakeExercise <- xmlGetWidget xml castToImageMenuItem "itemMakeExercise"
    itemSaveExercise <- xmlGetWidget xml castToImageMenuItem "itemSaveExercise"
    
    -- toolbuttons
    newProofTool <- xmlGetWidget xml castToToolButton "newProof"
    loadProofTool <- xmlGetWidget xml castToToolButton "loadProof"
    saveProofTool <- xmlGetWidget xml castToToolButton "saveProof"
    discardProofTool <- xmlGetWidget xml castToToolButton "discardProof"
    saveTheoremTool <- xmlGetWidget xml castToToolButton "saveTheoremTool"
    saveHypothesisTool <- xmlGetWidget xml castToToolButton "saveHypothesisTool"

    unDo <- xmlGetWidget xml castToToolButton "undoTool"
    reDo <- xmlGetWidget xml castToToolButton "redoTool"
    
    toolbarBox <- xmlGetWidget xml castToHBox "toolbarBox"
    
    fieldProofFaceBox <- xmlGetWidget xml castToHBox "fieldProofFaceBox"
    
    proofFaceBox <- xmlGetWidget xml castToHBox "proofFaceBox"
    
    showProofItem <- xmlGetWidget xml castToImageMenuItem "showProofPanelItem"
    showTypesItem <- xmlGetWidget xml castToImageMenuItem "showTypesPanelItem"
    
    -- Expresión inicial
    initExprBox <- xmlGetWidget xml castToHBox "initExprBox"
    
    -- Validar Prueba
    validTool <- xmlGetWidget xml castToToolButton "validateTool"
    itemValidateProof <- xmlGetWidget xml castToImageMenuItem "itemValidateProof"
    boxValidIcon <- xmlGetWidget xml castToHBox "boxValidIcon"
    imageValidProof <- imageNewFromStock iconUnknownProof IconSizeSmallToolbar
    boxPackStart boxValidIcon  imageValidProof PackNatural 2
    
    symGoLeftBox <- xmlGetWidget xml castToHBox "symGoLeftBox"
    symGoRightBox <- xmlGetWidget xml castToHBox "symGoRightBox"
    swSymbolList <- xmlGetWidget xml castToScrolledWindow "swSymbolList"
    
    truthBox <- io $ vBoxNew False 2

    windowMaximize window

    gRef <- newRef $ initialState window symbolList axiomList Nothing statusBar ctxExpr imageValidProof

    -- Agregamos los botones pero sin visibilidad.
    evalStateT (setupExerciseToolbar toolbarBox) gRef
    
    onActivateLeaf quitButton $ quitAction window
    onDestroy window mainQuit

    sListStore <- io $ setupSymbolList symbolList 
    setupScrolledWindowSymbolList swSymbolList symGoLeftBox symGoRightBox gRef
    aListStore <- io $ setupTruthList [] axiomList 
        
    -- Define la misma acción para el boton que para el menu
    -- convención: "nombreItem" (para item de menu) y "nombreTool" (para botón)
    getAndSetAction xml "saveHypothesis" (addHypothesisUI aListStore) gRef

    -- expresion inicial
    evalStateT (initExprState emptyExpr) gRef
    initExprWidget <- evalStateT (loadExpr initExprBox holePreExpr id) gRef

    setActionMenuTool itemNewProof newProofTool (createNewProof Nothing centralBox truthBox initExprWidget) gRef    

    setActionMenuTool itemSaveProof saveProofTool saveProofDialog gRef    
    setActionMenuTool itemDiscardProof discardProofTool (discardProof centralBox initExprWidget) gRef
    setActionMenuTool itemValidateProof validTool (checkProof imageValidProof truthBox) gRef
    
    setActionMenuTool itemUndo unDo (undoEvent centralBox truthBox initExprWidget) gRef
    setActionMenuTool itemRedo reDo (redoEvent centralBox truthBox initExprWidget) gRef
    
    onActivateLeaf itemMakeExercise $ 
                   evalStateT (showAllItemTool toolbarBox >> makeExercise) gRef 
    onActivateLeaf itemSaveExercise $ 
                   evalStateT (saveExercise) gRef 
    
    onActivateLeaf itemSaveAsTheorem $ saveTheorem gRef aListStore
    onToolButtonClicked saveTheoremTool $ saveTheorem gRef aListStore

    onToolButtonClicked loadProofTool $ dialogLoadProof gRef centralBox truthBox initExprWidget


    onActivateLeaf itemLoadProof $ dialogLoadProof gRef centralBox truthBox initExprWidget
    
    flip evalStateT gRef $ do
        axioms <- getAxiomCtrl
        eventsTruthList axioms aListStore
        symbols <- getSymCtrl
        runReaderT (eventsSymbolList symbols sListStore) (initExprWidget,id,ProofMove Just)
        hidePane errPane

    widgetShowAll window

    mainGUI
          
-- | Funcion que define el mismo evento para un menuItem y un toolButton.
setActionMenuTool item tool act ref = onToolButtonClicked tool action >>
                                      onActivateLeaf item action
    where action = evalStateT act ref 

-- TODO: unificar nombres de botones y menú de items de manera que se pueda
-- usar la funcion getAndSetAction
-- | Funcion que dado el nombre de un control que está en el menu y en la barra
-- configura la misma acción para ambos.
getAndSetAction xml name action ref = do
  item <- xmlGetWidget xml castToImageMenuItem $ name ++ "Item"
  tool <- xmlGetWidget xml castToToolButton $ name ++ "Tool"
  setActionMenuTool item tool action ref