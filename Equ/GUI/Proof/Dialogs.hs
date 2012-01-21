module Equ.GUI.Proof.Dialogs where

import Equ.GUI.Types
import Equ.GUI.State
import Equ.GUI.Utils
import Equ.GUI.Settings
import Equ.GUI.Proof 
import Equ.Proof

import Graphics.UI.Gtk hiding (eventButton, eventSent,get)

import Control.Monad.State (evalStateT,get)

import qualified Data.Foldable as F (mapM_)



dialogLoadProof :: GRef -> VBox -> VBox -> HBox -> IO ()
dialogLoadProof ref centralBox truthBox exprBox = do
    dialog <- fileChooserDialogNew (Just "Cargar Prueba") 
                                  Nothing 
                                  FileChooserActionOpen
                                  [ ("Cargar",ResponseAccept)
                                  , ("Cancelar",ResponseCancel)]

    equFileFilter dialog 
    response <- io $ dialogRun dialog
    
    case response of
         ResponseAccept -> do
             selected <- io $ fileChooserGetFilename dialog
             io $ debug ("aceptar clicked. Selected is " ++ show selected)
             flip F.mapM_ selected (\ filepath -> 
                                    decodeFile filepath >>= \proof ->
                                    evalStateT (createNewProof (Just proof) centralBox truthBox exprBox) ref >>
                                    widgetDestroy dialog)
         _ -> io $ widgetDestroy dialog

saveProofDialog :: IRG
saveProofDialog = do
    dialog <- io $ fileChooserDialogNew (Just "Guardar Prueba") 
                                       Nothing 
                                       FileChooserActionSave 
                                       [ ("Guardar",ResponseAccept)
                                       , ("Cancelar",ResponseCancel)]
                                   
    equFileFilter dialog                                   
    response <- io $ dialogRun dialog
    
    case response of
         ResponseAccept -> do
             selected <- io $ fileChooserGetFilename dialog
             io $ debug ("aceptar clicked. Selected is " ++ show selected)
             F.mapM_ saveProof selected
         _ -> return ()
    io $ widgetDestroy dialog
                         
saveProof :: FilePath -> IRG
saveProof filepath = getProof >>= io . encodeFile filepath . toProof

equFileFilter dialog = io $ setFileFilter dialog "*.equ" "Prueba de Equ"