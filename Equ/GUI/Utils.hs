{-# Language OverloadedStrings,TypeSynonymInstances,Rank2Types, ExistentialQuantification #-}
module Equ.GUI.Utils where

import Equ.GUI.Types

import Equ.Expr
import Equ.PreExpr
import Equ.Theories
import Equ.Types
import Equ.Syntax
import Equ.Parser

import Graphics.UI.Gtk hiding (eventButton, eventSent)
import Graphics.UI.Gtk.Gdk.EventM
import Graphics.UI.Gtk.Glade
import Data.Text
import Data.IORef
import Data.Maybe(fromJust)
import Control.Monad(liftM)
import Control.Monad.IO.Class(liftIO)

holeExpr = preExprHole ""

go :: (Focus -> Maybe Focus) -> Focus -> Focus
go g e = maybe (error $ show e) id $ g e

(.^.) :: GoBack -> GoBack -> GoBack
(f,f') .^. (g,g') = (f . g , g' . f')

(.^) :: (Focus -> Maybe Focus,Focus -> Maybe Focus) -> GoBack -> GoBack
(f,f') .^ (g,g') = (go f . g , g' . go f')

showExpr :: RExpr -> (Statusbar,ContextId) -> IO ()
showExpr r (s,c) = readIORef r >>= statusbarPush s c . show . toExpr . expr >> return ()


updateQVar :: String -> IRExpr
updateQVar v r _ sb = readIORef r >>= \gst -> 
                      case (expr gst) of 
                        (Quant q _ rng trm,p) -> writeIORef r $ gst {expr = (exp q v rng trm ,p) }
                        _ -> return () 
                      >> showExpr r sb
    where exp q v r t  = Quant q (var (pack v) TyUnknown) r t


updateExpr :: PreExpr -> IRExpr
updateExpr e r (f,f') sb = readIORef r >>= \gst -> 
                           (return . snd . f . expr) gst >>= \p ->
                           (writeIORef r) (gst { expr = f' (e, p) }) >>
                           showExpr r sb


updateFrmCtrl :: HBox -> RExpr -> IO ()
updateFrmCtrl l r = readIORef r >>= \gst -> writeIORef r $ gst { inpFocus = l }

updateSymCtrl :: TreeView -> RExpr -> IO ()
updateSymCtrl t r = readIORef r >>= \gst -> writeIORef r $ gst { symCtrl = t }

updatePath :: GoBack -> RExpr -> IO ()
updatePath p r = readIORef r >>= \gst -> writeIORef r $ gst { path = p }

getFrmCtrl :: RExpr -> IO HBox
getFrmCtrl r = readIORef r >>= return . inpFocus

getSymCtrl :: RExpr -> IO TreeView
getSymCtrl r = readIORef r >>= return . symCtrl

getPath :: RExpr -> IO GoBack
getPath r = readIORef r >>= return . path

data Boxeable w = forall w . WidgetClass w => Boxeable w

infixr 8 .*.

(.*.) :: (WidgetClass w') => w' -> [Boxeable w] -> [Boxeable w]
w .*. ws = Boxeable w : ws

infix 9 .*:
(.*:) :: (WidgetClass w',WidgetClass w) => w' -> w -> [Boxeable w]
w' .*: w = Boxeable w' : Boxeable w : []
