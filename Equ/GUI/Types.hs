{-# Language ImpredicativeTypes, ExistentialQuantification, TypeSynonymInstances, MultiParamTypeClasses #-}
module Equ.GUI.Types where

import Equ.PreExpr

import Graphics.UI.Gtk (WidgetClass, Statusbar, ContextId, HBox, TreeView,EventBox)
import Control.Monad.State
import Data.Reference
import Data.IORef

-- | Un movimiento es simplemente cambiar el foco.
type Move = Focus -> Focus

-- | Si @(f,g) :: GoBack@, entonces @f . g = id = g . f@.
type GoBack = (Move,Move)

-- | Si @(f,g) :: GoBack@, entonces @f . g = id = g . f@.
type MGoBack = (Focus -> Maybe Focus,Focus -> Maybe Focus)

type StatusPlace = (Statusbar, ContextId)

-- | El estado de nuestra interfaz.
data GState = GState { expr :: Focus       -- ^ La expresión que estamos editando.
                     , inpFocus  :: HBox   -- ^ El contenedor de la expresión.
                     , symCtrl :: TreeView -- ^ La lista de símbolos para construir expresiones.
                     , path :: GoBack      -- ^ Como ir de la expresión actual al top.
                     , status :: StatusPlace -- ^ La barra de estado.
                     }

-- | Una referencia polimórfica (ver Data.Reference).
type GRef = IORef GState

-- | El estado de nuestro programa encapsula una referencia junto con
-- una computación en IO.
type IState = StateT GRef IO

type IRExpr = IState ()

data WExpr w = WExpr { widget :: WidgetClass w => w
                     , wexpr :: PreExpr
                     }

data Boxeable w = forall w . WidgetClass w => Boxeable w


instance Reference IORef IState where
    readRef = liftIO . readRef
    writeRef r = liftIO . writeRef r
    newRef = liftIO . newRef