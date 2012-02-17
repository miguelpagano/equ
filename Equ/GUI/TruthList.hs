-- | Configuración de la lista de símbolos.
module Equ.GUI.TruthList where

import Equ.GUI.Types
import Equ.GUI.State
import Equ.GUI.Widget
import Equ.GUI.Expr
import Equ.GUI.Utils
import Equ.GUI.Settings


import Equ.Theories
import Equ.Syntax
import Equ.Proof
import qualified Equ.Proof.Proof as P
import Graphics.UI.Gtk hiding (eventButton, eventSent,get)
import Graphics.UI.Gtk.Gdk.Events 

import Data.Text(unpack,pack)
import Data.Maybe
import Data.Map (empty,elems)
import Data.Tree

import Control.Monad(liftM, when)
import Control.Monad.Trans(liftIO)
import qualified Data.Foldable as F (mapM_) 

type TruthItem = (String, HBox -> IRG)

-- | La lista de axiomas y teoremas; el primer elemento nos permite ingresar
-- una expresión en una caja de texto y parsearla.
listTruths :: [TheoryName] -> [Theorem] -> IO (TreeStore TruthItem)
listTruths available theoremList = treeStoreNew $ forest axioms 
                                      ++ forest theorems 
                                      ++ forest hypothesis
    where theorems = [(pack "Teoremas", theoremList)]
          hypothesis :: Grouped Hypothesis
          hypothesis = [(pack "Hipótesis", [])]

          forest ::  (Truth t, Show t) => Grouped t -> Forest TruthItem
          forest = toForest (\x -> (unpack x, const $ return ())) addItem  
                   
          axioms = filter (\x -> fst x `elem` available) axiomGroup

addItem :: (Truth t, Show t) => t -> TruthItem
addItem t = (show t, writeTruth $ truthBasic t)


writeTruth :: Basic -> HBox -> IRG
writeTruth basic b = do
    removeAllChildren b
    label <- io (labelNew (Just $ show basic))
    styleFont <- io styleStepEvidence
    io $ widgetModifyFont label (Just styleFont)
    io $ boxPackStart b label PackNatural 0
    (old_proof,path) <- getProof
    updateProofUndo (simpleProof (old_proof,path) basic)
    validateStep
    io $ widgetShowAll b

-- | La configuración de la lista de símbolos propiamente hablando.
setupTruthList :: [TheoryName] -> [Theorem] -> TreeView -> Window -> IO (TreeStore TruthItem)
setupTruthList available theoremList tv pwin  = 
    listTruths available theoremList >>= setupTList tv 

setupTList :: TreeView  -> TreeStore TruthItem -> IO (TreeStore TruthItem)
setupTList tv list = 
    treeViewGetColumn tv 0 >>=
    F.mapM_ (\c -> treeViewRemoveColumn tv c) >>
    treeViewColumnNew >>= \col ->
    treeViewSetHeadersVisible tv False >>
    treeViewSetModel tv list >>
    cellRendererTextNew >>= \renderer ->
    cellLayoutPackStart col renderer False >>
    cellLayoutSetAttributes col renderer list (\ind -> [ cellText := fst ind ]) >>
    treeViewAppendColumn tv col >>
    return list


-- | Funcion útil para cuando cargamos un ejercicio; mantiene las
-- hipótesis y los teoremas al definir los axiomas que se muestran de
-- acuerdo al ejercicio.
changeTruthList :: [TheoryName] -> TreeView -> IRG
changeTruthList available tv = getGlobalCtx >>= \ hyps ->
                               getTheorems >>= \ thms ->
                               io (listTruths available thms) >>= \ ts ->
                               io (mapM_ (addHypoList ts) (elems hyps)) >>
                               io (setupTList tv ts >> return ())

eventsTruthList :: TreeView -> TreeStore TruthItem -> IRG
eventsTruthList tv list = io (treeViewGetSelection tv >>= \tree -> 
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
oneSelection :: TreeStore (String,HBox -> IRG) -> TreeSelection -> IRG
oneSelection list tree = io (treeSelectionGetSelectedRows tree) >>= \sel ->
                           when (not (null sel)) $ return (head sel) >>= \h ->
                               io (treeStoreGetValue list h) >>= \(repr,acc) ->
                               getAxiomBox' >>= F.mapM_ acc



addTruthList :: (Truth t, Show t) => TreeStore TruthItem -> t -> Int -> IO ()
addTruthList truthList truth idx = treeStoreInsert truthList [idx] 0 (addItem truth)

addTheoList :: TreeStore TruthItem -> Theorem -> IO ()
addTheoList tl t = treeModelIterNChildren tl Nothing >>= \i -> addTruthList tl t (i-2) 

addHypoList :: TreeStore TruthItem -> Hypothesis -> IO ()
addHypoList tl h = treeModelIterNChildren tl Nothing >>= \i -> addTruthList tl h (i-1) 
