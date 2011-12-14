-- | Interfaz gráfica de Equ.
module Equ.GUI.Gui where

import Equ.GUI.Types
import Equ.GUI.Utils
import Equ.GUI.Widget
import Equ.GUI.Settings
import Equ.GUI.Expr
import Equ.GUI.SymbolList

import Graphics.UI.Gtk hiding (eventButton, eventSent,get)
import Graphics.UI.Gtk.Gdk.Events 
import Graphics.UI.Gtk.Glade
import Data.Text (pack,unpack)

import Data.Reference

import Control.Monad.State (evalStateT,get)
import Control.Monad(liftM, when)
import Control.Monad.Trans(liftIO)

main :: IO ()
main = do 
    initGUI

    -- TODO: qué pasa si no existe el archivo.
    Just xml <- xmlNew "Equ/GUI/equ2.glade"

    -- get widgets
    window        <- xmlGetWidget xml castToWindow "mainWindow"
    quitButton    <- getMenuButton xml "QuitButton"
    formWidget    <- xmlGetWidget xml castToHBox "formWidget"
    formBox       <- xmlGetWidget xml castToHBox "formulaBox"
    newExprButton <- xmlGetWidget xml castToToolButton "newExprButton"
    loadFormListButton <- xmlGetWidget xml castToToolButton "loadFormListButton"
    saveFormListButton <- xmlGetWidget xml castToToolButton "saveFormListButton"
    exprEdit      <- xmlGetWidget xml castToToolButton "exprEdit"
    exprInEdit      <- xmlGetWidget xml castToToolButton "exprInEdit"
    exprTree      <- xmlGetWidget xml castToToolButton "exprTree"
    saveExpr      <- xmlGetWidget xml castToToolButton "saveExpr"
    checkType      <- xmlGetWidget xml castToToolButton "checkType"
    exprTop       <- xmlGetWidget xml castToToolButton "exprTop"
    exprRemove    <- xmlGetWidget xml castToToolButton "exprRemove"
    exprRemoveAll <- xmlGetWidget xml castToToolButton "exprRemoveAll"
    closeTEPaneButton   <- xmlGetWidget xml castToToolButton "closeTEPane"
    clearButton   <- xmlGetWidget xml castToButton "clearButton"
    applyButton   <- xmlGetWidget xml castToButton "applyButton"
    statusBar     <- xmlGetWidget xml castToStatusbar "statusBar"
    ctxExpr       <- statusbarGetContextId statusBar "Expr"
    symbolList    <- xmlGetWidget xml castToTreeView "symbolList"
    typedFormBox  <- xmlGetWidget xml castToVBox "typedFormBox"

    symPane   <- xmlGetWidget xml castToPaned "symPane"
    formPane  <- xmlGetWidget xml castToPaned "formPane"
    errPane <- xmlGetWidget xml castToPaned "errPane"
    typedOptionPane <- xmlGetWidget xml castToHPaned "typedOptionPane"
    typedFormPane <- xmlGetWidget xml castToVPaned "typedFormPane"
    
    loadProof <- xmlGetWidget xml castToToolButton "loadProof"
    saveProof <- xmlGetWidget xml castToToolButton "saveProof"
    
    fieldProofFaceBox <- xmlGetWidget xml castToVBox "fieldProofFaceBox"
    
    faces <- xmlGetWidget xml castToNotebook "faces"
    proofFaceBox <- xmlGetWidget xml castToHBox "proofFaceBox"
    exprFaceBox <- xmlGetWidget xml castToHBox "exprFaceBox"
    boxGoProofFace <- xmlGetWidget xml castToHBox "boxGoProofFace"
    boxGoExprFace <- xmlGetWidget xml castToHBox "boxGoExprFace"
    
    windowMaximize window

    exprRef <- newRef $ GState emptyExpr
                               formBox
                               typedOptionPane
                               (TypedPaned typedFormPane Nothing [] [] [])
                               symbolList
                               (id,id)
                               (statusBar,ctxExpr)

    onActivateLeaf quitButton $ quitAction window
    onDestroy window mainQuit

    flip evalStateT exprRef $ 
        configArrowToProof faces boxGoProofFace >>
        configArrowToExpr faces boxGoExprFace >>
        hideTypedOptionPane >>
        hideTypedFormPane >>
        hideFormPane formBox errPane >>
        hideFormPane formBox formPane >>
        hideSymPane >>
        setupForm formBox >>
        setupSymbolList symbolList >>
        liftIO (clearButton `on` buttonPressEvent $ tryEvent $ 
                            eventWithState (hideFormPane formWidget errPane >>
                                            clearFocus formBox >> return ()) 
                            exprRef) >>
        liftIO (applyButton `on` buttonPressEvent $ tryEvent $ 
                            eventWithState (hideFormPane formWidget errPane >>
                                            hideFormPane formWidget formPane >> 
                                            hideSymPane >>
                                            updateTypedList)
                            exprRef) >>
        withState (onToolButtonClicked loadProof) 
                  (loadDummyProof fieldProofFaceBox) >>
        withState (onToolButtonClicked saveProof) 
                  (saveDummyProof) >>
        withState (onToolButtonClicked newExprButton) 
                  (newExpr formBox >> return ()) >>
        withState (onToolButtonClicked loadFormListButton) 
                  (loadFormList) >>
        withState (onToolButtonClicked saveFormListButton) 
                  (saveFormList) >>
        withState (onToolButtonClicked closeTEPaneButton) 
                  (hideTypedFormPane >> 
                   cleanTypedFormPane >>
                   cleanTypedTreeExpr >>
                   hideTypedOptionPane) >>
        withState (onToolButtonClicked exprEdit) 
                  (typedExprEdit formBox) >>
        withState (onToolButtonClicked exprInEdit) 
                  (typedExprInEdit) >>
        withState (onToolButtonClicked exprTree) 
                  (cleanTypedFormPane >> 
                   cleanTypedTreeExpr >> 
                   typedExprTree) >>
        withState (onToolButtonClicked saveExpr) 
                  (cleanTypedFormPane >> 
                   cleanTypedTreeExpr >> 
                   hideTypedOptionPane >>
                   hideTypedFormPane >>
                   saveTypedExpr) >>
        withState (onToolButtonClicked checkType) 
                  (typedCheckType) >>
        withState (onToolButtonClicked exprTop) 
                  (hideTypedFormPane >> cleanTypedFormPane) >>
        withState (onToolButtonClicked exprRemove)
                  (typedExprRemove >> 
                   hideTypedOptionPane) >>
        withState (onToolButtonClicked exprRemoveAll)
                  (typedExprRemoveAll >> 
                   hideTypedFormPane >> 
                   cleanTypedFormPane >>
                   hideTypedOptionPane)
    widgetShowAll window
    mainGUI
