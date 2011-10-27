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
    exprTree      <- xmlGetWidget xml castToToolButton "exprTree"
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
    
    windowMaximize window

    exprRef <- newRef $ GState emptyExpr
                               formBox
                               typedOptionPane
                               (TypedPaned typedFormPane [] [])
                               symbolList
                               (id,id)
                               (statusBar,ctxExpr)

    onActivateLeaf quitButton $ quitAction window
    onDestroy window mainQuit

    flip evalStateT exprRef $ 
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
        withState (onToolButtonClicked newExprButton) 
                  (newExpr formBox >> return ()) >>
        withState (onToolButtonClicked loadFormListButton) 
                  (loadFormList) >>
        withState (onToolButtonClicked saveFormListButton) 
                  (saveFormList) >>
        withState (onToolButtonClicked closeTEPaneButton) 
                  (hideTypedFormPane >> 
                   cleanTypedFormPane >>
                   hideTypedOptionPane) >>
        withState (onToolButtonClicked exprEdit) 
                  (typedExprEdit) >>
        withState (onToolButtonClicked exprTree) 
                  (typedExprTree) >>
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
