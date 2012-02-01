module Equ.GUI.Proof.Dialogs where

import Equ.GUI.Types
import Equ.GUI.State
import Equ.GUI.Utils
import Equ.GUI.Settings
import Equ.GUI.Proof 
import Equ.Proof

import Graphics.UI.Gtk hiding (eventButton, eventSent,get)

import Data.Maybe(isJust)
import Control.Monad(when)
import qualified Data.Foldable as F (mapM_)



dialogLoadProof :: GRef -> VBox -> VBox -> ExprWidget -> IO ()
dialogLoadProof ref centralBox truthBox expr_w = do
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
                                    evalStateT (createNewProof (Just proof) centralBox truthBox expr_w) ref >>
                                    widgetDestroy dialog)
         _ -> io $ widgetDestroy dialog

saveProofDialog :: IRG
saveProofDialog = do
    pf <- getProofState
    when (isJust pf) $ do 
      dialog <- io $ fileChooserDialogNew (Just "Guardar Prueba") 
                                         Nothing 
                                         FileChooserActionSave 
                                         [ ("Guardar",ResponseAccept)
                                         , ("Cancelar",ResponseCancel)]
                                   
      equFileFilter dialog                                   
      response <- io $ dialogRun dialog
    
      case response of
        ResponseAccept -> io (fileChooserGetFilename dialog) >>= F.mapM_ saveProof
        _ -> return ()
      io $ widgetDestroy dialog
                         
saveProof :: FilePath -> IRG
saveProof filepath = getProof >>= io . encodeFile filepath . toProof

equFileFilter dialog = io $ setFileFilter dialog "*.equ" "Prueba de Equ"