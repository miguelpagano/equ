{-# Language OverloadedStrings,TypeSynonymInstances,Rank2Types, ExistentialQuantification #-}
-- | Interfaz gráfica de Equ.
module Equ.GUI.Gui where

import Equ.GUI.Types
import Equ.GUI.Utils
import Equ.GUI.Widget

import Equ.Expr
import Equ.PreExpr
import Equ.Theories
import Equ.Types
import Equ.Syntax
import Equ.Parser

import Graphics.UI.Gtk hiding (eventButton, eventSent)
import Graphics.UI.Gtk.Gdk.Events 
import Graphics.UI.Gtk.Glade
import Data.Text (pack,unpack)
import Data.IORef
import Control.Monad(liftM, when)

getMenuButton w = xmlGetWidget w castToMenuItem 


listSymbols = listStoreNew $ map addItem quantifiersList
                          ++ map addItem operatorsList
                          ++ map addItem constantsList
                          ++ [ ("Variable",  writeVarExp)
                             , ("Expresión", writeExpr) 
                             ]

    where addItem :: (Syntactic s,ExpWriter s) => s -> (String, HBox -> IRExpr)
          addItem syn = (unpack $ tRepr syn, writeExp syn)

setupSymbolList :: TreeView -> IRExpr
setupSymbolList tv r f sb = 
    treeViewColumnNew >>= \col ->
    listSymbols >>= \list ->   
    treeViewSetHeadersVisible tv False >>
    cellRendererTextNew >>= \renderer ->
    cellLayoutPackStart col renderer False >>
    cellLayoutSetAttributes col renderer list (\ind -> [cellText := fst ind]) >>
    treeViewAppendColumn tv col >>
    treeViewGetSelection tv >>= \tree -> 
    treeSelectionSetMode tree SelectionSingle >>
    treeSelectionUnselectAll tree >>
    treeViewSetModel tv list >>
    onSelectionChanged tree (oneSelection list tree r f sb) >>
    widgetShowAll tv


oneSelection :: ListStore (String,HBox -> IRExpr) -> TreeSelection -> IRExpr
oneSelection list tree r f sb = treeSelectionGetSelectedRows tree >>= \sel ->
                                when (not (null sel)) $ return (head sel) >>= \h ->
                                    when (not (null h)) $ return (head h) >>= \s ->
                                        listStoreGetValue list s >>= \(repr,acc) ->
                                        getPath r >>= \p ->
                                        getFrmCtrl r >>= \b -> acc b r p sb

main :: IO ()
main = do
    initGUI
    
    Just xml <- xmlNew "Equ/GUI/equ2.glade"

    -- get widgets
    window <- xmlGetWidget xml castToWindow "mainWindow"

    quitButton <- getMenuButton xml "QuitButton"

    formLabel <- xmlGetWidget xml castToLabel "formulaLabel"
    formBox <- xmlGetWidget xml castToHBox "formulaBox"

    clearButton <- xmlGetWidget xml castToButton "clearButton"

    statusBar <- xmlGetWidget xml castToStatusbar "statusBar"
    ctxExpr <- statusbarGetContextId statusBar "Expr"

    symbolList <- xmlGetWidget xml castToTreeView "symbolList"


    exprRef <- newIORef $ GState (toFocus holeExpr) formBox symbolList (id,id)

    setupForm formBox exprRef (id,id) (statusBar,ctxExpr)
    setupSymbolList symbolList exprRef (id,id) (statusBar,ctxExpr)
    onPressed clearButton $ clearExpr formBox exprRef (id,id) (statusBar,ctxExpr)
    
    onActivateLeaf quitButton $ quitAction window
    onDestroy window mainQuit

    widgetShowAll window
    mainGUI
