-- | Configuración de la lista de símbolos.
module Equ.GUI.TruthList where

import Equ.GUI.Types
import Equ.GUI.Utils
import Equ.GUI.Widget
import Equ.GUI.Expr

import Equ.Theories
import Equ.Syntax
import Equ.Proof
import qualified Equ.Proof.Proof as P

import Graphics.UI.Gtk hiding (eventButton, eventSent,get)
import Graphics.UI.Gtk.Gdk.Events 

import Data.Text(unpack)
import Data.Maybe
import Data.Map (empty)

import Control.Monad(liftM, when)
import Control.Monad.Trans(liftIO)

-- | La lista de axiomas y teoremas; el primer elemento nos permite ingresar
-- una expresión en una caja de texto y parsearla.
listTruths :: IO (ListStore (String, HBox -> IRProof))
listTruths = listStoreNew $ map addItem axiomList
    where addItem :: (Truth t, Show t) => t -> (String, HBox -> IRProof)
          addItem t = (show t, writeTruth t)
          
writeTruth :: (Truth t, Show t) => t -> HBox -> IRProof
writeTruth t b = do
    removeAllChildren b
    label <- liftIO (labelNew (Just $ show t))
    liftIO $ boxPackStart b label PackGrow 0
    (old_proof,path) <- getProof
    updateProof (simpleProof (old_proof,path) $ truthBasic t)
--     updateProof (Simple empty (fromJust $ P.getRel old_proof) 
--                 (fromJust $ P.getStart old_proof) (fromJust $ P.getEnd old_proof) 
--                 (truthBasic t))
    liftIO $ widgetShowAll b

-- | La configuración de la lista de símbolos propiamente hablando.
setupTruthList :: TreeView -> IO (ListStore (String,HBox -> IRProof))
setupTruthList tv = 
     treeViewColumnNew >>= \col ->
     listTruths >>= \list -> 
     treeViewSetHeadersVisible tv False >>
     cellRendererTextNew >>= \renderer ->
     cellLayoutPackStart col renderer False >>
     cellLayoutSetAttributes col renderer list (\ind -> [cellText := fst ind]) >>
     treeViewAppendColumn tv col >> return list

eventsTruthList :: TreeView -> ListStore (String,HBox -> IRProof) -> IRProof
eventsTruthList tv list =
     liftIO(treeViewGetSelection tv >>= \tree -> 
     treeSelectionSetMode tree SelectionSingle >>
     treeSelectionUnselectAll tree >>
     treeViewSetModel tv list >> widgetShowAll tv >> return tree) >>= \tree ->
     withState (onSelectionChanged tree) (oneSelection list tree) >> return ()
     
     
-- | Handler para cuando cambia el símbolo seleccionado. La acción es
-- inmediata; es decir, al pasar de uno a otro se muestra
-- automáticamente (el widget de) la nueva expresión en la caja
-- correspondiente. Una opción es que se vaya cambiando pero que al
-- poner Enter recién se haga el cambio real y entonces desaparezca la
-- lista de símbolos.
oneSelection :: ListStore (String,HBox -> IRProof) -> TreeSelection -> IRProof
oneSelection list tree = liftIO (treeSelectionGetSelectedRows tree) >>= \sel ->
                           when (not (null sel)) $ return (head sel) >>= \h ->
                               when (not (null h)) $ return (head h) >>= \s ->
                                   liftIO (listStoreGetValue list s) >>= \(repr,acc) ->
                                   getAxiomBox >>= acc