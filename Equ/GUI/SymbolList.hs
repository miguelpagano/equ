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
import qualified Graphics.UI.Gtk as G
import Graphics.UI.Gtk.Gdk.Events 

import Data.Text(unpack)

import Control.Monad(liftM, when)
import Control.Monad.Reader
import qualified Data.Foldable as F

type SynItem = (String, HBox -> IExpr' ())
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

eventsSymbolList :: IconView -> ListStore SynItem -> IExpr' ()
eventsSymbolList tv list = do s <- get
                              env <- ask
                              io $ tv `on` itemActivated $ \path -> flip evalStateT s $
                                 runReaderT (oneSelection list path) env
                              return ()


setupScrolledWindowSymbolList :: ScrolledWindow -> HBox -> HBox -> GRef -> IO ()
setupScrolledWindowSymbolList sw goLb goRb s = do
            goR <- makeScrollArrow goRb stockGoForward
            goL <- makeScrollArrow goLb stockGoBack
            (Just  swslH) <- scrolledWindowGetHScrollbar sw
            adj <- rangeGetAdjustment swslH
            setupScrollWithArrow adj goR scrollInc s
            setupScrollWithArrow adj goL scrollDec s
            widgetSetChildVisible swslH False
            widgetHide swslH

setupScrollWithArrow :: Adjustment -> Button -> Double -> GRef -> IO (ConnectId Button)
setupScrollWithArrow adj go inc s = go `on` buttonPressEvent $ tryEvent $ 
                                    flip eventWithState s $ io $ do
                                         val <- adjustmentGetValue adj
                                         upper <- adjustmentGetUpper adj
                                         pageSize <- adjustmentGetPageSize adj
                                         if upper - pageSize > val + inc 
                                         then adjustmentSetValue adj (val + inc)
                                         else return ()

makeScrollArrow :: HBox -> StockId -> IO Button
makeScrollArrow box si = do
                        symGo <- buttonNew
                        
                        buttonSetRelief symGo ReliefNone
                        
                        arrow <- imageNewFromStock si IconSizeMenu
                        
                        buttonSetImage symGo arrow
                        
                        boxPackStart box symGo PackNatural 0
                        return symGo

     

-- | Handler para cuando cambia el símbolo seleccionado. La acción es
-- inmediata; es decir, al pasar de uno a otro se muestra
-- automáticamente (el widget de) la nueva expresión en la caja
-- correspondiente. Una opción es que se vaya cambiando pero que al
-- poner Enter recién se haga el cambio real y entonces desaparezca la
-- lista de símbolos.
oneSelection :: ListStore SynItem -> TreePath -> IExpr' ()
oneSelection list path = io (getElem list path) >>= 
                         F.mapM_ (\(_,acc) -> lift getFrmCtrl >>= acc)

getElem :: ListStore a -> TreePath -> IO (Maybe a)
getElem l p = treeModelGetIter l p >>= \i ->
              flip (maybe (return Nothing)) i $ \it -> 
                        return (listStoreIterToIndex it) >>= \idx ->
                        listStoreGetSize l >>= \len -> 
                        debug ( "getElem: (" ++ show idx ++ " of " ++ show len ++")") >>
                        if (idx < len) 
                        then listStoreGetValue l idx >>= return . Just
                        else return Nothing
