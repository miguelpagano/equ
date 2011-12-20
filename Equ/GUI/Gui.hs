-- | Interfaz gráfica de Equ.
module Equ.GUI.Gui where

import Equ.GUI.Types
import Equ.GUI.Utils
import Equ.GUI.Widget
import Equ.GUI.Settings
import Equ.GUI.Expr
import Equ.GUI.SymbolList
import Equ.GUI.TruthList
import Equ.GUI.Proof
import Equ.PreExpr(toFocus)
import Equ.Proof
import Equ.Parser

import Equ.Rule (relEq)

import qualified Graphics.UI.Gtk as G
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
    Just xml <- xmlNew "Equ/GUI/equ.glade"

    -- get widgets
    window        <- xmlGetWidget xml castToWindow "mainWindow"
    quitButton    <- getMenuButton xml "QuitButton"
    --formWidget    <- xmlGetWidget xml castToHBox "formWidget"
    --formWidget    <- createFormWidget
    formWidgetBox       <- xmlGetWidget xml castToHBox "formBox"
    newExprButton <- xmlGetWidget xml castToToolButton "newExprButton"
    --clearButton   <- xmlGetWidget xml castToButton "clearButton"
    --applyButton   <- xmlGetWidget xml castToButton "applyButton"
    statusBar     <- xmlGetWidget xml castToStatusbar "statusBar"
    ctxExpr       <- statusbarGetContextId statusBar "Expr"
    symbolList    <- xmlGetWidget xml castToTreeView "symbolList"
    axiomList     <- xmlGetWidget xml castToTreeView "axiomList"
    --typedFormBox  <- xmlGetWidget xml castToVBox "typedFormBox"

    --symPane   <- xmlGetWidget xml castToPaned "symPane"
    symFrame <- xmlGetWidget xml castToFrame "symFrame"
    axiomFrame <- xmlGetWidget xml castToFrame "axiomFrame"
    formPane  <- xmlGetWidget xml castToPaned "formPane"
    errPane <- xmlGetWidget xml castToPaned "errPane"
    
    centralBox <- xmlGetWidget xml castToVBox "centralBox"
    itemNewProof <- xmlGetWidget xml castToImageMenuItem "itemNewProof"
    itemLoadProof <- xmlGetWidget xml castToImageMenuItem "itemLoadProof"

    --formWidget <- createFormWidget formWidgetBox

--     exprRef <- newRef $ GState emptyExpr
--                                (formBox formWidget)
--                                symbolList
--                                (id,id)
--                                (statusBar,ctxExpr)
--                                axiomList
--                                (toProofFocus (newProof relEq emptyExpr emptyExpr))

    onActivateLeaf quitButton $ quitAction window
    onDestroy window mainQuit
    sListStore <- setupSymbolList symbolList
    aListStore <- setupTruthList axiomList
    onActivateLeaf itemNewProof (createNewProof Nothing centralBox symbolList sListStore axiomList aListStore (statusBar,ctxExpr))
    onActivateLeaf itemLoadProof (createNewProof test_proof centralBox symbolList sListStore axiomList aListStore (statusBar,ctxExpr))
    
    widgetShowAll window

--     flip evalStateT exprRef $ 
--         hideFormPane (formBox formWidget) errPane >>
--         hideFormPane (formBox formWidget) formPane >>
--         hideSymFrame >> hideAxiomFrame >>
--         setupForm (formBox formWidget) >>
--         setupSymbolList symbolList >>
--         liftIO ((clearButton formWidget) `on` buttonPressEvent $ tryEvent $ 
--                             eventWithState (hideFormPane (extBox formWidget) errPane >>
--                                             clearFocus (formBox formWidget) >> return ()) 
--                             exprRef) >>
-- --         liftIO ((applyButton formWidget) `on` buttonPressEvent $ tryEvent $ 
-- --                             eventWithState (hideFormPane (extBox formWidget) errPane >>
-- --                                             hideFormPane (extBox formWidget) formPane >> 
-- --                                             hideSymPane >>
-- --                                             updateTypedList typedFormBox) 
-- --                             exprRef) >>
--         withState (onToolButtonClicked newExprButton) 
--                     (newExpr (formBox formWidget) >> return ())

    -- widgetShowAll formPane
    
    --widgetShowAll window
    --flip evalStateT exprRef (newExpr (formBox formWidget) >> return ())
    mainGUI
    
    where test_proof = Just $ newProof relEq (toFocus $ parser "1 + 1") (toFocus $ parser "0") 
          
          
