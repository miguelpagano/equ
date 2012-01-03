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
import Equ.GUI.TypeTree
import Equ.PreExpr(toFocus, toFocuses, agrupOp, agrupNotOp, opOfFocus)
import Equ.Proof
import Equ.Parser
import Equ.Theories

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
    saveExpr      <- xmlGetWidget xml castToToolButton "saveExpr"
    checkType      <- xmlGetWidget xml castToToolButton "checkType"

    statusBar     <- xmlGetWidget xml castToStatusbar "statusBar"
    ctxExpr       <- statusbarGetContextId statusBar "Expr"
    symbolList    <- xmlGetWidget xml castToTreeView "symbolList"
    axiomList     <- xmlGetWidget xml castToTreeView "axiomList"
    
    symFrame <- xmlGetWidget xml castToFrame "symFrame"
    axiomFrame <- xmlGetWidget xml castToFrame "axiomFrame"
    errPane <- xmlGetWidget xml castToPaned "errPane"

    centralBox <- xmlGetWidget xml castToVBox "centralBox"
    itemNewProof <- xmlGetWidget xml castToImageMenuItem "itemNewProof"
    itemLoadProof <- xmlGetWidget xml castToImageMenuItem "itemLoadProof"
    itemSaveProof <- xmlGetWidget xml castToImageMenuItem "itemSaveProof"
    itemSaveAsTheorem <- xmlGetWidget xml castToImageMenuItem "itemSaveAsTheorem"
    
    faces <- xmlGetWidget xml castToNotebook "faces"
    
    loadProof <- xmlGetWidget xml castToToolButton "loadProof"
    saveProof <- xmlGetWidget xml castToToolButton "saveProof"
    
    fieldProofFaceBox <- xmlGetWidget xml castToHBox "fieldProofFaceBox"
    fieldExprFaceBox <- xmlGetWidget xml castToVBox "fieldExprFaceBox"
    
    proofFaceBox <- xmlGetWidget xml castToHBox "proofFaceBox"
    exprFaceBox <- xmlGetWidget xml castToHBox "exprFaceBox"
    boxGoProofFace <- xmlGetWidget xml castToHBox "boxGoProofFace"
    boxGoExprFace <- xmlGetWidget xml castToHBox "boxGoExprFace"

    windowMaximize window

    gRef <- newRef $ initialState symbolList axiomList faces statusBar ctxExpr

    onActivateLeaf quitButton $ quitAction window
    onDestroy window mainQuit

    sListStore <- liftIO $ setupSymbolList symbolList
    aListStore <- liftIO $ setupTruthList [] axiomList 

    onActivateLeaf itemNewProof (evalStateT (createNewProof Nothing centralBox sListStore) gRef)
    onActivateLeaf itemLoadProof $ dialogLoadProof gRef centralBox sListStore
    onActivateLeaf itemSaveProof (evalStateT (saveProofDialog) gRef)
    onActivateLeaf itemSaveAsTheorem $ saveTheorem gRef aListStore
    
    flip evalStateT gRef $ do
        axioms <- getAxiomCtrl
        eventsTruthList axioms aListStore
        hidePane errPane
        switchToProof faces boxGoProofFace (cleanTypedExprTree >> cleanTreeExpr)
        switchToTypeTree faces boxGoExprFace typedExprTree
        withState (onToolButtonClicked checkType) typedCheckType

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
          
          
dialogLoadProof :: GRef -> VBox ->
                   ListStore (String,HBox -> IRG) -> IO ()
dialogLoadProof ref centralBox sListStore = do
    dialog <- fileChooserDialogNew (Just "Cargar Prueba") Nothing FileChooserActionOpen
                                [("Cargar",ResponseAccept),("Cancelar",ResponseCancel)]
    setFileFilter dialog "*.equ" "Prueba de Equ"
    response <- liftIO $ dialogRun dialog
    
    case response of
         ResponseAccept -> do
             selected <- liftIO $ fileChooserGetFilename dialog
             liftIO $ putStrLn ("aceptar clicked. Selected is " ++ show selected)
             case selected of
                  Just filepath -> decodeFile filepath >>= \proof ->
                                flip evalStateT ref
                                  (createNewProof (Just proof) centralBox sListStore) >>
                                  widgetDestroy dialog
                  Nothing -> widgetDestroy dialog
         _ -> liftIO $ widgetDestroy dialog

saveProofDialog :: IRG
saveProofDialog = do
    dialog <- liftIO $ fileChooserDialogNew (Just "Guardar Prueba") Nothing FileChooserActionSave 
                                   [("Guardar",ResponseAccept),("Cancelar",ResponseCancel)]
                                   
    liftIO $ setFileFilter dialog "*.equ" "Prueba de Equ"
                                   
    response <- liftIO $ dialogRun dialog
    
    case response of
         ResponseAccept -> do
             selected <- liftIO $ fileChooserGetFilename dialog
             liftIO $ putStrLn ("aceptar clicked. Selected is " ++ show selected)
             case selected of
                  Just filepath -> saveProof filepath >> (liftIO $ widgetDestroy dialog)
                  Nothing -> liftIO $ widgetDestroy dialog
         _ -> liftIO $ widgetDestroy dialog
                         
saveProof :: FilePath -> IRG
saveProof filepath = getProof >>= \pf -> liftIO $ encodeFile filepath (toProof pf)

saveTheorem :: GRef -> ListStore (String, HBox -> IRG) -> IO ()
saveTheorem ref aListStore = evalStateT (updateValidProof >> checkValidProof) ref >>= \valid ->
                             putStrLn ("valid is " ++ show valid) >>
                             if valid then saveTheoremDialog ref aListStore
                                      else errorDialog "La prueba no es válida"

-- | Dialogo para guardar una prueba como teorema de Equ. Asume que la prueba es válida.

saveTheoremDialog :: GRef -> ListStore (String, HBox -> IRG) -> IO ()
saveTheoremDialog ref aListStore = do
    dialog <- dialogNew
    set dialog [windowTitle := "Guardar Teorema"]
    dialogAddButton dialog stockApply ResponseApply
    dialogAddButton dialog stockCancel ResponseCancel
    box <- dialogGetUpper dialog
    
    hbox1 <- hBoxNew False 2
    labelName <- labelNew $ Just "Nombre del teorema:"
    entry <- liftIO entryNew
    boxPackStart hbox1 labelName PackNatural 2
    boxPackStart hbox1 entry PackNatural 2
    
    hbox2 <- hBoxNew False 2
    labelExprTitle <- labelNew $ Just "Expresión:"
    labelExpr <- labelNew Nothing
    boxPackStart hbox2 labelExprTitle PackNatural 2
    boxPackStart hbox2 labelExpr PackNatural 2
    
    boxPackStart box hbox1 PackNatural 2
    boxPackStart box hbox2 PackNatural 2
    
    evalStateT (getExprProof >>= \expr ->
                liftIO $ labelSetText labelExpr (show expr)) ref
    
    widgetShowAll box
    
    response <- dialogRun dialog
    if response==ResponseApply
       then entryGetText entry >>= \th_name ->
            evalStateT (getValidProof >>= return . fromRight >>= \proof ->
                        addTheorem (createTheorem (pack th_name) proof) >>= \theo ->
                        liftIO $ listStoreAppend aListStore (addItem theo)) ref >>
            widgetDestroy dialog
            
       else widgetDestroy dialog
       
    where addItem :: (Truth t, Show t) => t -> (String, HBox -> IRG)
          addItem t = (show t, writeTruth $ truthBasic t)
    
          
          
-- reloadAxioms :: IState ()
-- reloadAxioms = do
--     liftIO $ putStrLn "reloading axioms..."
--     theoremList <- getTheorems
--     liftIO $ putStrLn $ "theoremList is " ++ show theoremList
--     axioms <- getAxiomCtrl
--     liftIO $ putStrLn "setupTruthList: "
--     aListStore <- liftIO $ setupTruthList theoremList axioms 
--     lista <- liftIO $ listStoreToList aListStore
--     liftIO $ putStrLn $ "aListStore is: " ++ show (map fst lista)
--     liftIO $ putStrLn "eventsTruthList: "
--     axioms <- getAxiomCtrl
--     eventsTruthList axioms aListStore
--     return ()
    
