{-# Language OverloadedStrings,TypeSynonymInstances,Rank2Types, ExistentialQuantification #-}
-- | Interfaz gráfica de Equ.
module Equ.GUI.Gui where

import Equ.GUI.Utils
import Equ.Expr
import Equ.PreExpr
import Equ.Theories
import Equ.Types
import Equ.Syntax
import Equ.Parser

import Graphics.UI.Gtk hiding (eventButton, eventSent)
import Graphics.UI.Gtk.Gdk.Events 
import Graphics.UI.Gtk.Glade
import Data.Text
import Data.IORef
import Data.Maybe(fromJust)
import Control.Monad(liftM)

getMenuButton w = xmlGetWidget w castToMenuItem 


main :: IO ()
main = do
    initGUI




    Just xml <- xmlNew "Equ/GUI/equ.glade"
    exprRef <- emptyRef

    -- get widgets
    window <- xmlGetWidget xml castToWindow "mainWindow"

    quitButton <- getMenuButton xml "QuitButton"

    formBox <- xmlGetWidget xml castToHBox "formulaBox"
    exprButton <- xmlGetWidget xml castToButton "addButton"
    clearButton <- xmlGetWidget xml castToButton "clearButton"

    statusBar <- xmlGetWidget xml castToStatusbar "statusBar"
    ctxExpr <- statusbarGetContextId statusBar "Expr"


    menuSymbols <- menuNew
    loadItems menuSymbols formBox exprRef (id,id) (statusBar,ctxExpr)

    -- signals
    onPressed exprButton $ menuPopup menuSymbols Nothing
    onPressed clearButton $ clearExpr formBox exprRef (id,id) (statusBar,ctxExpr)
    
    widgetShowAll menuSymbols

    onActivateLeaf quitButton $ quitAction window
    onDestroy window mainQuit

    widgetShowAll window
    mainGUI
