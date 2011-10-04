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

main :: IO ()
main = do
    initGUI
    Just xml <- xmlNew "Equ/GUI/interfaz1.glade"
    exprRef <- emptyRef

    -- get widgets
    window <- xmlGetWidget xml castToWindow "window1"
    formBox <- xmlGetWidget xml castToHBox "box_formula"
    exprButton <- xmlGetWidget xml castToButton "button_expr"
    applyButton <- xmlGetWidget xml castToButton "applyButton"
    quitButton <- getMenuButton xml "QuitButton"

    statusBar <- xmlGetWidget xml castToStatusbar "statusBar"
    ctxExpr <- statusbarGetContextId statusBar "Expr"


    menuSymbols <- menuNew
    loadItems menuSymbols formBox exprRef (id,id) (statusBar,ctxExpr)

    -- signals
    onPressed exprButton $ menuPopup menuSymbols Nothing
    onPressed applyButton $ menuPopup menuSymbols Nothing
    onActivateLeaf quitButton $ quitAction window
    onDestroy window mainQuit
    
    widgetShowAll menuSymbols
    widgetShowAll window
    mainGUI
