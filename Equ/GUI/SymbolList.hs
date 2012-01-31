-- | Configuración de la lista de símbolos.
module Equ.GUI.SymbolList where

import Equ.GUI.Types
import Equ.GUI.State
import Equ.GUI.Expr
import Equ.GUI.Settings
import Equ.GUI.Utils

import Equ.Theories
import Equ.Syntax

import Graphics.UI.Gtk hiding (eventButton, eventSent,get)
import Graphics.UI.Gtk.Gdk.Events 

import Data.Text(unpack)

import Control.Monad.State(get,evalStateT)
import Control.Monad(liftM, when)
import Control.Monad.Trans(liftIO)
import qualified Data.Foldable as F

type SynItem = (String, HBox -> IRG)
-- TODO: pensar que esta lista podría ser extendida si el usuario
-- define un conjunto de símbolos de función o de constantes.
-- | La lista de símbolos; el primer elemento nos permite ingresar
-- una expresión en una caja de texto y parsearla.
listSymbols :: IO (ListStore SynItem)
listSymbols = listStoreNew $ map (addItem) quantifiersList
                          ++ map (addItem) operatorsList
                          ++ map (addItem) constantsList

    where addItem :: (Syntactic s,ExpWriter s) =>  s -> SynItem
          addItem syn = (unpack $ tRepr syn, writeExp syn)

-- | La configuración de la lista de símbolos propiamente hablando.
setupSymbolList :: IconView -> IO (ListStore SynItem)
setupSymbolList tv = 
     listSymbols >>= \list -> 
     return (makeColumnIdString 1) >>= \scol ->
     return (makeColumnIdPixbuf (-1)) >>= \pcol ->
     iconViewSetTextColumn tv scol >>
     iconViewSetPixbufColumn tv pcol >>
     customStoreSetColumn list scol fst >>
     set tv [ iconViewModel := Just list
            , iconViewPixbufColumn := pcol
            , iconViewTextColumn := scol
            , iconViewColumns := 24
            , iconViewRowSpacing := 0
            , iconViewMargin := 0] >>
     widgetShowAll tv >>
     return list

setupScrolledWindowSymbolList :: ScrolledWindow -> EventBox -> EventBox -> 
                                 GRef -> IO ()
setupScrolledWindowSymbolList sw goL goR s = do
            (Just  swslH) <- scrolledWindowGetHScrollbar sw
            adj <- rangeGetAdjustment swslH
            setupScrollWithArrow adj goR scrollInc s
            setupScrollWithArrow adj goL scrollDec s
            widgetSetChildVisible swslH False
            widgetHide swslH

setupScrollWithArrow :: Adjustment -> EventBox -> Double -> 
                        GRef -> IO (ConnectId EventBox)
setupScrollWithArrow adj go inc s = 
        go `on` buttonPressEvent $ tryEvent $ 
            flip eventWithState s (do 
                                   val <- io $ adjustmentGetValue adj
                                   upper <- io $ adjustmentGetUpper adj
                                   pageSize <- io $ adjustmentGetPageSize adj
                                   if upper - pageSize > val + inc then
                                       io $ adjustmentSetValue adj (val + inc)
                                   else
                                       return ()
                                  )    

eventsSymbolList :: IconView -> ListStore SynItem -> IRG
eventsSymbolList tv list = get >>= \s ->                           
                           liftIO (tv `on` itemActivated $ flip evalStateT s . (oneSelection list)) >>
                           return ()
     

-- | Handler para cuando cambia el símbolo seleccionado. La acción es
-- inmediata; es decir, al pasar de uno a otro se muestra
-- automáticamente (el widget de) la nueva expresión en la caja
-- correspondiente. Una opción es que se vaya cambiando pero que al
-- poner Enter recién se haga el cambio real y entonces desaparezca la
-- lista de símbolos.
oneSelection :: ListStore SynItem -> TreePath -> IRG
oneSelection list path = liftIO (getElem list path) >>= \i ->
                         flip F.mapM_ i $ \(repr,acc) -> getFrmCtrl >>= acc

getElem :: ListStore a -> TreePath -> IO (Maybe a)
getElem l p = treeModelGetIter l p >>= \i ->
              flip (maybe (return Nothing)) i $ \it -> 
                        return (listStoreIterToIndex it) >>= \idx ->
                        listStoreGetSize l >>= \len -> 
                        putStrLn ( "getElem: (" ++ show idx ++ " of " ++ show len ++")") >>
                        if (idx < len) 
                        then listStoreGetValue l idx >>= return . Just
                        else return Nothing
