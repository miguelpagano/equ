{-# Language DoAndIfThenElse #-}
-- | Configuración de la lista de símbolos.
module Equ.GUI.SymbolList where

import Equ.GUI.Types
import Equ.GUI.State
import Equ.GUI.State.Expr
import Equ.GUI.State.SymbolList
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
            , iconViewMargin := 0
            ] >>
     widgetShowAll tv >>
     return list



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
                                         val <- io $ adjustmentGetValue adj
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
