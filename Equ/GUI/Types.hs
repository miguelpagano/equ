{-# Language OverloadedStrings,TypeSynonymInstances,Rank2Types, ExistentialQuantification #-}
module Equ.GUI.Types where

import Equ.PreExpr

import Graphics.UI.Gtk (WidgetClass, Statusbar, ContextId, HBox, TreeView)
import Data.IORef

data GState = GState { expr :: Focus
                     , inpFocus  :: HBox
                     , symCtrl :: TreeView
                     }


type RExpr = IORef GState
type IState' m a = RExpr -> (Focus -> Focus,Focus -> Focus) -> (Statusbar, ContextId) -> m a
type IState a = IState' IO a

type IRExpr = IState ()

data WExpr w = WExpr { widget :: WidgetClass w => w
                     , getExpr :: PreExpr
                     }

type GoBack = (Focus -> Focus,Focus -> Focus)


