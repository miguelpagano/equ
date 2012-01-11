-- | Configuración de la lista de símbolos.
module Equ.GUI.SymbolList where

import Equ.GUI.Types
import Equ.GUI.State
import Equ.GUI.Expr

import Equ.Theories
import Equ.Syntax

import Graphics.UI.Gtk hiding (eventButton, eventSent,get)
import Graphics.UI.Gtk.Gdk.Events 

import Data.Text(unpack)

import Control.Monad(liftM, when)
import Control.Monad.Trans(liftIO)

-- TODO: pensar que esta lista podría ser extendida si el usuario
-- define un conjunto de símbolos de función o de constantes.
-- | La lista de símbolos; el primer elemento nos permite ingresar
-- una expresión en una caja de texto y parsearla.
listSymbols :: IO (ListStore (String, HBox -> IRG))
listSymbols = listStoreNew $ ("Expresión", writeExpr):
                             map addItem quantifiersList
                          ++ map addItem operatorsList
                          ++ map addItem constantsList

    where addItem :: (Syntactic s,ExpWriter s) => s -> (String, HBox -> IRG)
          addItem syn = (unpack $ tRepr syn, writeExp syn)

setupSymbolListBeta :: IconView -> IO (ListStore (String,HBox -> IRG))
setupSymbolListBeta iv = listSymbols >>= \list ->
                         listStoreGetSize list >>= \sizeList ->
                         iconViewSetColumns iv sizeList >>
                         iconViewSetSelectionMode iv SelectionSingle >>
                         iconViewSetModel iv (Just list) >>
                         return list
                         --setupSymbolListBeta' iv 0
{-
setupSymbolListBeta' :: IconView -> Int -> IO (ListStore (String,HBox -> IRG))
setupSymbolListBeta' _ 0 = listSymbols >>= return
setupSymbolListBeta' tv i = treeViewColumnNew >>= \col ->
                            listSymbols >>= \list -> 
                            treeViewSetHeadersVisible tv False >>
                            cellRendererTextNew >>= \renderer ->
                            listStoreGetValue list i >>= \val ->
                            set renderer [cellText := fst val] >>
                            treeViewColumnPackStart col renderer False >>
                            treeViewAppendColumn tv col >>
                            setupSymbolListBeta' tv (i-1)-}

-- | La configuración de la lista de símbolos propiamente hablando.
setupSymbolList :: TreeView -> IO (ListStore (String,HBox -> IRG))
setupSymbolList tv = 
     treeViewColumnNew >>= \col ->
     listSymbols >>= \list -> 
     treeViewSetHeadersVisible tv False >>
     cellRendererTextNew >>= \renderer ->
     cellLayoutPackStart col renderer False >>
     cellLayoutSetAttributes col renderer list (\ind -> [cellText := fst ind]) >>
     treeViewAppendColumn tv col >> return list

eventsSymbolList :: TreeView -> ListStore (String,HBox -> IRG) -> IRG
eventsSymbolList tv list =
     liftIO (treeViewGetSelection tv >>= \tree -> 
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
oneSelection :: ListStore (String,HBox -> IRG) -> TreeSelection -> IRG
oneSelection list tree = 
                        liftIO (treeSelectionGetSelectedRows tree) >>= \sel ->
                           when (not (null sel)) $ return (head sel) >>= \h ->
                               when (not (null h)) $ return (head h) >>= \s ->
                                   liftIO (listStoreGetValue list s) >>= \(repr,acc) ->
                                   getFrmCtrl >>= acc
