-- | Interfaz gráfica de Equ.
module Equ.GUI.Gui where

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

--     cleanType    <- xmlGetWidget xml castToToolButton "cleanType"
--     checkType    <- xmlGetWidget xml castToToolButton "checkType"

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
    itemSaveAsTheorem <- xmlGetWidget xml castToImageMenuItem "itemSaveAsTheorem"
    
    itemUndo <- xmlGetWidget xml castToImageMenuItem "undoMenuItem"
    itemRedo <- xmlGetWidget xml castToImageMenuItem "redoMenuItem"
    
    --faces <- xmlGetWidget xml castToNotebook "faces"
    faces <- notebookNew
    -- toolbuttons
    newProofTool <- xmlGetWidget xml castToToolButton "newProof"
    loadProofTool <- xmlGetWidget xml castToToolButton "loadProof"
    saveProofTool <- xmlGetWidget xml castToToolButton "saveProof"
    
    unDo <- xmlGetWidget xml castToToolButton "undoTool"
    reDo <- xmlGetWidget xml castToToolButton "redoTool"
    
    fieldProofFaceBox <- xmlGetWidget xml castToHBox "fieldProofFaceBox"
    --fieldExprFaceBox <- xmlGetWidget xml castToVBox "fieldExprFaceBox"
    
    proofFaceBox <- xmlGetWidget xml castToHBox "proofFaceBox"
    
    showProofItem <- xmlGetWidget xml castToImageMenuItem "showProofPanelItem"
    showTypesItem <- xmlGetWidget xml castToImageMenuItem "showTypesPanelItem"
    
    -- Validar Prueba
    validTool <- xmlGetWidget xml castToToolButton "validateTool"
    itemValidateProof <- xmlGetWidget xml castToImageMenuItem "itemValidateProof"
    boxValidIcon <- xmlGetWidget xml castToHBox "boxValidIcon"
    imageValidProof <- imageNewFromStock iconUnknownProof IconSizeSmallToolbar
    boxPackStart boxValidIcon  imageValidProof PackNatural 2
    
    truthBox <- io $ vBoxNew False 2

    windowMaximize window

    gRef <- newRef $ initialState window symbolList axiomList faces statusBar ctxExpr imageValidProof

    onActivateLeaf quitButton $ quitAction window
    onDestroy window mainQuit

    sListStore <- liftIO $ setupSymbolList symbolList
    aListStore <- liftIO $ setupTruthList [] axiomList 

    onToolButtonClicked newProofTool (evalStateT (createNewProof Nothing centralBox truthBox) gRef)
    onActivateLeaf itemNewProof (evalStateT (createNewProof Nothing centralBox truthBox) gRef)
    onToolButtonClicked loadProofTool $ dialogLoadProof gRef centralBox truthBox
    onActivateLeaf itemLoadProof $ dialogLoadProof gRef centralBox truthBox 
    onToolButtonClicked saveProofTool (evalStateT (saveProofDialog) gRef)
    onActivateLeaf itemSaveProof (evalStateT (saveProofDialog) gRef)
    onActivateLeaf itemSaveAsTheorem $ saveTheorem gRef aListStore
    
    
    onActivateLeaf itemUndo $ flip evalStateT gRef $ undoEvent centralBox truthBox
    onToolButtonClicked unDo $ flip evalStateT gRef $ undoEvent centralBox truthBox
    
    onActivateLeaf itemRedo $ flip evalStateT gRef $ redoEvent centralBox truthBox
    onToolButtonClicked reDo $ flip evalStateT gRef $ redoEvent centralBox truthBox
    
    onToolButtonClicked validTool (evalStateT (checkProof imageValidProof truthBox) gRef)
    onActivateLeaf itemValidateProof $ flip evalStateT gRef $ checkProof imageValidProof truthBox
    
    flip evalStateT gRef $ do
        axioms <- getAxiomCtrl
        eventsTruthList axioms aListStore
        symbols <- getSymCtrl
        eventsSymbolList symbols sListStore
        hidePane errPane

    widgetShowAll window

    mainGUI

    where undoEvent centralBox truthBox = 
                        liftIO (debug "Undo event") >>
                        getUndoList >>= \ulist ->
                        case ulist of
                             [] -> liftIO (debug "lista undo vacia") >> return ()
                             [p] -> liftIO (debug "lista undo con un solo elemento") >> return ()
                             p':p:ps -> setNoUndoing >>
                                    (F.forM_ (urProof p) $
                                    \pf -> createNewProof (Just $ toProof pf) centralBox truthBox) >>
                                    updateUndoList (p:ps) >>
                                    setUndoing >>
                                    addToRedoList p'
                                    
                        >>
                        getUndoList >>= \ulist' ->
                        liftIO (debug $ "UndoList es " ++ show ulist')
                        
          redoEvent centralBox truthBox =
                        liftIO (debug "Redo event") >>
                        getRedoList >>= \rlist ->
                        case rlist of
                             [] -> liftIO (debug "lista redo vacia") >> return ()
                             p:ps -> setNoUndoing >>
                                   (F.forM_ (urProof p) $
                                   \pf -> createNewProof (Just $ toProof pf) centralBox truthBox) >>
                                   updateRedoList ps >>
                                   addToUndoListFromRedo p >>
                                   setUndoing
          
dialogLoadProof :: GRef -> VBox -> VBox -> IO ()
dialogLoadProof ref centralBox truthBox = do
    dialog <- fileChooserDialogNew (Just "Cargar Prueba") 
                                  Nothing 
                                  FileChooserActionOpen
                                  [ ("Cargar",ResponseAccept)
                                  , ("Cancelar",ResponseCancel)]

    setFileFilter dialog "*.equ" "Prueba de Equ"
    response <- liftIO $ dialogRun dialog
    
    case response of
         ResponseAccept -> do
             selected <- liftIO $ fileChooserGetFilename dialog
             liftIO $ debug ("aceptar clicked. Selected is " ++ show selected)
             case selected of
                  Just filepath -> decodeFile filepath >>= \proof ->
                                flip evalStateT ref
                                  (createNewProof (Just proof) centralBox truthBox) >>
                                  widgetDestroy dialog
                  Nothing -> widgetDestroy dialog
         _ -> liftIO $ widgetDestroy dialog

saveProofDialog :: IRG
saveProofDialog = do
    dialog <- liftIO $ fileChooserDialogNew (Just "Guardar Prueba") 
                                           Nothing 
                                           FileChooserActionSave 
                                           [ ("Guardar",ResponseAccept)
                                           , ("Cancelar",ResponseCancel)]
                                   
    liftIO $ setFileFilter dialog "*.equ" "Prueba de Equ"
                                   
    response <- liftIO $ dialogRun dialog
    
    case response of
         ResponseAccept -> do
             selected <- liftIO $ fileChooserGetFilename dialog
             liftIO $ debug ("aceptar clicked. Selected is " ++ show selected)
             case selected of
                  Just filepath -> saveProof filepath >> return ()
                  Nothing -> return ()
         _ -> return ()
    liftIO $ widgetDestroy dialog
                         
saveProof :: FilePath -> IRG
saveProof filepath = getProof >>= \pf -> liftIO $ encodeFile filepath (toProof pf)


saveTheorem :: GRef -> TreeStore (String, HBox -> IRG) -> IO ()
saveTheorem ref aListStore = evalStateT (updateValidProof >> checkValidProof) ref >>= \valid ->
                             debug ("valid is " ++ show valid) >>
                             if valid then saveTheoremDialog ref aListStore
                                      else errorDialog "La prueba no es válida"

-- | Dialogo para guardar una prueba como teorema de Equ. Asume que la prueba es válida.

saveTheoremDialog :: GRef -> TreeStore (String, HBox -> IRG) -> IO ()
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
    case response of
      ResponseApply -> entryGetText entry >>= \th_name ->
                      evalStateT (getValidProof >>= return . fromRight >>= \proof ->
                                  addTheorem (createTheorem (pack th_name) proof) >>= \theo ->
                                  io idxTheorem >>= \idx ->
                                  liftIO $ treeStoreInsert aListStore [idx] 0 (addItem theo)) ref >>
                      return ()
      _ -> return ()
    widgetDestroy dialog
       
    where addItem :: (Truth t, Show t) => t -> (String, HBox -> IRG)
          addItem t = (show t, writeTruth $ truthBasic t)
          idxTheorem = treeModelIterNChildren aListStore Nothing >>= \len ->
                       return (len-1)
    
          
          
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
    
