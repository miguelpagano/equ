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
    where addItem :: (Syntactic s,ExpWriter s) => s -> (String, HBox -> IRExpr)
          addItem syn = (unpack $ tRepr syn, writeExp syn)
{-
loadItems :: (BoxClass b) => Menu -> b -> IRExpr
loadItems menu box r f sb = do
    appendItems quantifiersList
    appendItems operatorsList
    appendItems constantsList
    appendItemVariable 
    appendItemPreExpr
    
    where appendItems :: (Syntactic s,ExpWriter s) => [s] -> IO ()
          appendItems [] = return ()
          appendItems (x:xs) = do
              item <- menuItemNewWithLabel $ unpack $ tRepr x
              onActivateLeaf item $ writeExp x box r f sb
              menuShellAppend menu item
              appendItems xs
              
          appendItemVariable = do
              item <- menuItemNewWithLabel "Variable"
              onActivateLeaf item (writeVarExp box r f sb)
              menuShellAppend menu item
              
          appendItemPreExpr = do
              item <- menuItemNewWithLabel "Expresión"
              onActivateLeaf item (writeExpr box r f sb)
              menuShellAppend menu item
              
-}

setupSymbolList :: TreeView -> IRExpr
setupSymbolList tv r f sb = 
    treeViewColumnNew >>= \col ->
    listSymbols >>= \list ->   
    treeViewSetModel tv list >>
    treeViewSetHeadersVisible tv False >>
    cellRendererTextNew >>= \renderer ->
    cellLayoutPackStart col renderer False >>
    cellLayoutSetAttributes col renderer list (\ind -> [cellText := fst ind]) >>
    treeViewAppendColumn tv col >>
    treeViewGetSelection tv >>= \tree -> 
    treeSelectionSetMode tree  SelectionSingle >>
    onSelectionChanged tree (oneSelection list tree r f sb) >>
    widgetShowAll tv

oneSelection :: ListStore (String,HBox -> IRExpr) -> TreeSelection -> IRExpr
oneSelection list tree r f sb = treeSelectionGetSelectedRows tree >>= \sel ->
                                when (not (null sel)) $ return (head sel) >>= \h ->
                                    when (not (null h)) $ return (head h) >>= \s ->
                                        listStoreGetValue list s >>= \(repr,acc) ->
                                        getFrmCtrl r >>= \b -> acc b r f sb

main :: IO ()
main = do
    initGUI
    
    Just xml <- xmlNew "Equ/GUI/equ2.glade"

    -- get widgets
    window <- xmlGetWidget xml castToWindow "mainWindow"

    quitButton <- getMenuButton xml "QuitButton"

    formLabel <- xmlGetWidget xml castToLabel "formulaLabel"
    formBox <- xmlGetWidget xml castToHBox "formulaBox"

    exprButton <- xmlGetWidget xml castToButton "addButton"
    clearButton <- xmlGetWidget xml castToButton "clearButton"

    statusBar <- xmlGetWidget xml castToStatusbar "statusBar"
    ctxExpr <- statusbarGetContextId statusBar "Expr"

    symbolList <- xmlGetWidget xml castToTreeView "symbolList"


    exprRef <- newIORef $ GState (toFocus holeExpr) formBox symbolList

    setupForm formBox exprRef (id,id) (statusBar,ctxExpr)
    setupSymbolList symbolList exprRef (id,id) (statusBar,ctxExpr)

--    menuSymbols <- menuNew
--    loadItems menuSymbols formBox exprRef (id,id) (statusBar,ctxExpr)


    -- signals
--    onPressed exprButton $ menuPopup menuSymbols Nothing
    onPressed clearButton $ clearExpr formBox exprRef (id,id) (statusBar,ctxExpr)
    
--    widgetShowAll menuSymbols

    onActivateLeaf quitButton $ quitAction window
    onDestroy window mainQuit

    widgetShowAll window
    mainGUI
