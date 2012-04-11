{-# Language DoAndIfThenElse #-}
-- | Configuración de la lista de símbolos.
module Equ.GUI.State.SymbolList where

import Equ.GUI.Types
import Equ.GUI.State.Internal
import Equ.GUI.State.Expr
import Equ.GUI.Settings
import Equ.GUI.Utils
import Graphics.UI.Gtk hiding (eventButton, eventSent,get)
import qualified Graphics.UI.Gtk as G
import Graphics.UI.Gtk.Gdk.Events 

import Control.Monad(liftM, when)
import Control.Monad.Reader
import qualified Data.Foldable as F

eventsSymbolList :: IconView -> ListStore SynItem -> IExpr' ()
eventsSymbolList tv list = do s <- get
                              env <- ask
                              cid <- io $ tv `on` itemActivated $ \path -> flip evalStateT s $
                                 runReaderT (oneSelection list path) env
                              oldCid <- lift getSymCid 
                              F.mapM_ (io . signalDisconnect) oldCid
                              lift $ updateSymCid (Just cid)
                              return ()

-- | Handler para cuando cambia el símbolo seleccionado. La acción es
-- inmediata; es decir, al pasar de uno a otro se muestra
-- automáticamente (el widget de) la nueva expresión en la caja
-- correspondiente. Una opción es que se vaya cambiando pero que al
-- poner Enter recién se haga el cambio real y entonces desaparezca la
-- lista de símbolos.
oneSelection :: ListStore SynItem -> TreePath -> IExpr' ()
oneSelection list path = io (getElem list path) >>= 
                         F.mapM_ (\(repr,acc) -> getFormBox >>= symbolOrBox repr acc)

-- | Si el primer hijo de la caja enfocada es un entry-box, entonces
-- insertamos el símbolo al final, en vez de remplazar ese entry-box
-- por una caja.
symbolOrBox :: ContainerClass self => String -> (self -> IExpr' ()) -> self -> IExpr' ()
symbolOrBox r replace box = liftIO (containerGetChildren box) >>= \chlds ->
                     if length chlds > 0
                     then if isA (head chlds) gTypeEntry
                          then liftIO (return (castToEntry (head chlds)) >>= \entry ->
                                       entryGetText entry >>= \expr ->
                                       widgetGrabFocus entry >>
                                       editableSelectRegion entry (length expr) (length expr) >>
                                       editableInsertText entry r (length expr) >>
                                       set entry [ editablePosition := (-1) ] >>
                                       return ())
                          else replace box
                     else replace box

getElem :: ListStore a -> TreePath -> IO (Maybe a)
getElem l p = treeModelGetIter l p >>= \i ->
              flip (maybe (return Nothing)) i $ \it -> 
                        return (listStoreIterToIndex it) >>= \idx ->
                        listStoreGetSize l >>= \len -> 
                        if (idx < len) 
                        then listStoreGetValue l idx >>= return . Just
                        else return Nothing

-- | Devuelve el ConnectId para eventos de iconview.
getSymCid :: IState (Maybe (ConnectId IconView))
getSymCid = getStatePartDbg "getSymCid" symCid


-- | Actualiza el CID del evento ItemActivated de la lista de símbolos
updateSymCid :: Maybe (ConnectId IconView) -> IState ()
updateSymCid cid = update $ \gst -> gst { symCid = cid }


getSymCtrl :: IState IconView
getSymCtrl = getStatePartDbg "getSymCtrl" symCtrl

getSymStore :: IState (ListStore SynItem)
getSymStore = getStatePartDbg "getSymStore" symStore
