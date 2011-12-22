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

import Equ.Rule (relEq,relEquiv)

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
    formWidgetBox       <- xmlGetWidget xml castToHBox "formBox"

    exprInEdit      <- xmlGetWidget xml castToToolButton "exprInEdit"
    exprTree      <- xmlGetWidget xml castToToolButton "exprTree"
    saveExpr      <- xmlGetWidget xml castToToolButton "saveExpr"
    checkType      <- xmlGetWidget xml castToToolButton "checkType"

    statusBar     <- xmlGetWidget xml castToStatusbar "statusBar"
    ctxExpr       <- statusbarGetContextId statusBar "Expr"
    symbolList    <- xmlGetWidget xml castToTreeView "symbolList"
    axiomList     <- xmlGetWidget xml castToTreeView "axiomList"
    
    symFrame <- xmlGetWidget xml castToFrame "symFrame"
    axiomFrame <- xmlGetWidget xml castToFrame "axiomFrame"
    errProofPane <- xmlGetWidget xml castToPaned "errProofPane"
    errExprPane <- xmlGetWidget xml castToPaned "errExprPane"

    centralBox <- xmlGetWidget xml castToVBox "centralBox"
    itemNewProof <- xmlGetWidget xml castToImageMenuItem "itemNewProof"
    itemLoadProof <- xmlGetWidget xml castToImageMenuItem "itemLoadProof"
    
    exprOptionPane <- xmlGetWidget xml castToHPaned "exprOptionPane"
    faces <- xmlGetWidget xml castToNotebook "faces"
    
    loadProof <- xmlGetWidget xml castToToolButton "loadProof"
    saveProof <- xmlGetWidget xml castToToolButton "saveProof"
    
    fieldProofFaceBox <- xmlGetWidget xml castToHBox "fieldProofFaceBox"
    fieldExprFaceBox <- xmlGetWidget xml castToHBox "fieldExprFaceBox"
    
    proofFaceBox <- xmlGetWidget xml castToHBox "proofFaceBox"
    exprFaceBox <- xmlGetWidget xml castToHBox "exprFaceBox"
    boxGoProofFace <- xmlGetWidget xml castToHBox "boxGoProofFace"
    boxGoExprFace <- xmlGetWidget xml castToHBox "boxGoExprFace"

    windowMaximize window

    gRef <- newRef $ GState Nothing
                            Nothing
                            []
                            symbolList
                            axiomList
                            exprOptionPane
                            faces
                            []
                            []
                            []
                            (Stadistic [])
                            (statusBar, ctxExpr)

    onActivateLeaf quitButton $ quitAction window
    onDestroy window mainQuit

    flip evalStateT gRef $ do
        configArrowToProof faces boxGoProofFace
        configArrowToExpr faces boxGoExprFace
        hidePane fieldProofFaceBox errProofPane
        hidePane fieldExprFaceBox errExprPane
        sListStore <- liftIO $ setupSymbolList symbolList
        aListStore <- liftIO $ setupTruthList axiomList 
        liftIO $ onActivateLeaf itemNewProof (evalStateT (createNewProof Nothing centralBox sListStore aListStore) gRef)
        withState (onToolButtonClicked exprTree) 
                  (typedExprTree)
--         hideTypedOptionPane >>
--         hideTypedFormPane >>
--         hidePane formBox errPane >>
--         hidePane formBox formPane >>
--         hideSymPane >>
--         setupForm formBox >>
--         setupSymbolList symbolList >>
--         withState (onToolButtonClicked closeTEPaneButton) 
--                   (hideTypedFormPane >> 
--                    cleanTypedFormPane >>
--                    cleanTypedTreeExpr >>
--                    hideTypedOptionPane) >>
--         withState (onToolButtonClicked exprEdit) 
--                   (typedExprEdit formBox) >>
--         withState (onToolButtonClicked exprInEdit) 
--                   (typedExprInEdit) >>
--         withState (onToolButtonClicked exprTree) 
--                   (cleanTypedFormPane >> 
--                    cleanTypedTreeExpr >> 
--                    typedExprTree) >>
--         withState (onToolButtonClicked saveExpr) 
--                   (cleanTypedFormPane >> 
--                    cleanTypedTreeExpr >> 
--                    hideTypedOptionPane >>
--                    hideTypedFormPane >>
--                    saveTypedExpr) >>
--         withState (onToolButtonClicked checkType) 
--                   (typedCheckType) >>
--         withState (onToolButtonClicked exprTop) 
--                   (hideTypedFormPane >> cleanTypedFormPane) >>
--         withState (onToolButtonClicked exprRemove)
--                   (typedExprRemove >> 
--                    hideTypedOptionPane) >>
--         withState (onToolButtonClicked exprRemoveAll)
--                   (typedExprRemoveAll >> 
--                    hideTypedFormPane >> 
--                    cleanTypedFormPane >>
--                    hideTypedOptionPane)
    widgetShowAll window

    mainGUI
    
--     where test_proof = Just $ newProof relEquiv (toFocus $ parser "1 + 1") (toFocus $ parser "0") 
          
          
