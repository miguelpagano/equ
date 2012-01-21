{-# Language ImpredicativeTypes, ExistentialQuantification, TypeSynonymInstances, MultiParamTypeClasses #-}
module Equ.GUI.Types where

import Equ.PreExpr

import Equ.Proof (Proof,PM,ProofFocus,Theorem,Hypothesis)
import Equ.Proof.Proof (Ctx)

import Graphics.UI.Gtk ( WidgetClass, Statusbar, ContextId, HBox, TreeView
                       , EventBox, Label, Button, Notebook, HPaned, IconView
                       , Window, Image
                       )

import Equ.Types

import Control.Monad.State
import Data.Reference
import Data.IORef

-- | Un movimiento es simplemente cambiar el foco.
type Move = Focus -> Focus

-- | Si @(f,g) :: GoBack@, entonces @f . g = id = g . f@.
type GoBack = (Move,Move)

-- | Si @(f,g) :: GoBack@, entonces @f . g = id = g . f@.
type MGoBack = (Focus -> Maybe Focus,Focus -> Maybe Focus)

data EditMask = Editable | NotEditable

type StatusPlace = (Statusbar, ContextId)

type UndoList = [URMove]
type RedoList = [URMove]
data URMove = URMove { urProof :: Maybe ProofFocus -- ^ Si guardamos una prueba. 
                     , urExpr :: Maybe Focus
                     }
instance Show URMove where
    show u = show (urProof u)

data Accion = Undo | Redo | InvalidCheck | ValidCheck 
 
type TGraph = [(Int, Int, Accion)]
 
data Statistic = Statistic { thinkingGraph :: TGraph }

-- TODO: hace falta? Eliminé el campo de GState y todo funciona bien. 
type RecentExprList = [PreExpr]

data TreeExpr = TreeExpr { mainExpr :: ExprState
                         , opExpr :: [[(Focus, Move)]]
                         , atomExpr :: [ExprState]
                         , quantExpr :: [ExprState]
                         }

data GState = GState { gWindow :: Window
                     , gProof :: Maybe ProofState -- ^ Prueba en progreso.
                     , gExpr :: Maybe ExprState -- ^ Expresión seleccionada.
                     , gTreeExpr :: Maybe TreeExpr -- ^ Árbol de una expresión.
                     , symCtrl :: IconView   -- ^ La lista de símbolos para construir expresiones.
                     , axiomCtrl :: TreeView -- ^ La lista de axiomas para construir pruebas.
                     , gFaces :: Notebook -- ^ Las distintas caras de la interfaz.
                     , gUndo :: UndoList -- ^ Undo.
                     , gRedo :: RedoList -- ^ Redo.
                     , gStatistic :: Statistic -- ^ Conjunto de estadisticas.
                     , status :: StatusPlace  -- ^ La barra de estado.
                     , theorems :: [Theorem]
                     , hypothesis :: Ctx -- ^ Hipotesis globales. Cuando se crea una prueba se copian al contexto.
                     , undoing :: Bool
                     , imageValid :: Image
                     }
 
data ExprState = ExprState { fExpr :: Focus
                           , fType :: Type
                           , pathExpr :: GoBack
                           , eventExpr :: HBox
                           , eventType :: HBox
                           }

data ProofState = ProofState { proof :: ProofFocus   -- ^ La prueba que estamos construyendo
                             , validProof :: PM Proof
                             , modifExpr :: ProofFocus -> Focus -> Maybe ProofFocus  
                                 -- ^ Funcion para modificar la expresion 
                                 --  enfocada DENTRO de la prueba.
                             , axiomBox :: HBox -- ^ El contenedor para mostrar el axioma aplicado
                             }

type GRef = IORef GState
type IState = StateT GRef IO
type IRG = IState () 

data WExpr w = WExpr { widget :: WidgetClass w => w
                     , wexpr :: PreExpr
                     }

data Boxeable w = forall w . WidgetClass w => Boxeable w

instance Reference IORef IState where
    readRef = liftIO . readRef
    writeRef r = liftIO . writeRef r
    newRef = liftIO . newRef

data ExprWidget = ExprWidget { extBox :: HBox       -- ^ Widget más externo.
                             , formBox :: HBox      -- ^ Box donde se ingresa la formula
                             , choicesButton :: Button -- ^ Botón para ver las expresiones que matchean en la prueba
                             }
