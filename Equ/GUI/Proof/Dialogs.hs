module Equ.GUI.Proof.Dialogs where

import Equ.GUI.Types
import Equ.GUI.State
import Equ.GUI.Utils
import Equ.GUI.Settings
import Equ.GUI.Proof 
import Equ.GUI.Widget
import Equ.Proof

import Graphics.UI.Gtk hiding (eventButton, eventSent,get)

import Data.Maybe(isJust)
import Control.Monad(when)
import qualified Data.Foldable as F (mapM_)

dialogLoadProof :: GRef -> VBox -> VBox -> ExprWidget -> IO ()
dialogLoadProof ref centralBox truthBox expr_w = do
        dialogLoad "Cargar prueba"
                   equFileFilter
                   (loadProof)
        return ()
    where
        loadProof :: Proof -> IO ()
        loadProof p = evalStateT (createNewProof (Just p) centralBox 
                                                 truthBox expr_w) ref

saveProofDialog :: IState ()
saveProofDialog = getProofState >>= \pf ->
               case pf of
                   Nothing -> makeErrWindow "Ninguna prueba para guardar."
                   Just _ -> getProof >>= \p ->
                             saveDialog "Guardar ejercicio"
                                        ""
                                        equFileFilter
                                        (toProof p) >> return ()

equFileFilter dialog = io $ setFileFilter dialog "*.equ" "Prueba de Equ"
