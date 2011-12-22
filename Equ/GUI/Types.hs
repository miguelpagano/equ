{-# Language ImpredicativeTypes, ExistentialQuantification, TypeSynonymInstances, MultiParamTypeClasses #-}
module Equ.GUI.Types where

import Equ.PreExpr
import Equ.Proof (Proof,PM,ProofFocus)

import Graphics.UI.Gtk (WidgetClass, Statusbar, ContextId, HBox, TreeView,EventBox, Label, Button)
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
data ExprFocus = ExprFocus { expr :: Focus       -- ^ La expresión que estamos editando.
                           --, proofPath :: ProofPath   -- ^ Path a la expresión en la prueba.
                           , path :: GoBack
                           , inpFocus :: HBox      -- ^ El contenedor de la expresión enfocada
                     }

-- | Una referencia polimórfica (ver Data.Reference).
type ExprRef = IORef ExprFocus

type ExprState = StateT ExprRef IO

type IRExpr = ExprState ()


data ProofState = ProofState { proof :: ProofFocus   -- ^ La prueba que estamos construyendo
                             , validProof :: PM Proof
                             , symCtrl :: TreeView   -- ^ La lista de símbolos para construir expresiones.
                             , focusedExpr :: ExprFocus      -- ^ Expresion enfocada
                             , modifExpr :: ProofFocus -> Focus -> Maybe ProofFocus  -- ^ Funcion para modificar la expresion enfocada DENTRO de la prueba. Esto sirve asi solo
                                                                     --   para el caso prueba simple, donde esta funcion puede ser updateStart o updateEnd.
                             , status :: StatusPlace  -- ^ La barra de estado.
                             , axiomCtrl :: TreeView -- ^ La lista de axiomas para construir pruebas.
                             , axiomBox :: HBox      -- ^ El contenedor para mostrar el axioma aplicado
                            }

type ProofRef = IORef ProofState

-- | El estado de nuestro programa encapsula una referencia junto con
-- una computación en IO.
type IState = StateT ProofRef IO

type IRProof = IState ()
                            

data WExpr w = WExpr { widget :: WidgetClass w => w
                     , wexpr :: PreExpr
                     }

data Boxeable w = forall w . WidgetClass w => Boxeable w


instance Reference IORef IState where
    readRef = liftIO . readRef
    writeRef r = liftIO . writeRef r
    newRef = liftIO . newRef
    
data ExprWidget = ExprWidget { extBox :: HBox       -- ^ Widget más externo.
                             , expLabel :: Label -- ^ Label con el texto "Expresión:"
                             , formBox :: HBox   -- ^ Box donde se ingresa la formula
                             , clearButton :: Button -- ^ Botón para borrar toda la expresión.
                             , applyButton :: Button -- ^ Botón para aplicar la expresión.
                             }
