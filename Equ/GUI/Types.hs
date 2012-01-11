{-# Language ImpredicativeTypes, ExistentialQuantification, TypeSynonymInstances, MultiParamTypeClasses #-}
module Equ.GUI.Types where

import Equ.PreExpr

import Equ.Proof (Proof,PM,ProofFocus,Theorem)

import Graphics.UI.Gtk ( WidgetClass, Statusbar, ContextId, HBox, TreeView
                       , EventBox, Label, Button, Notebook, HPaned
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


type StatusPlace = (Statusbar, ContextId)

type UndoList = [URMove]
type RedoList = [URMove]
data URMove = URMove { urProof :: Maybe ProofFocus -- ^ Si guardamos una prueba. 
                     }
instance Show URMove where
    show u = show (urProof u)

data Accion = Undo | Redo | InvalidCheck | ValidCheck 
 
type TGraph = [(Int, Int, Accion)]
 
data Statistic = Statistic { thinkingGraph :: TGraph }
 
type RecentExprList = [PreExpr]

data TreeExpr = TreeExpr { mainExpr :: ExprState
                         , opExpr :: [[(Focus, Move)]]
                         , atomExpr :: [ExprState]
                         , quantExpr :: [ExprState]
                         }

data GState = GState { gProof :: Maybe ProofState -- ^ Prueba en progreso.
                     , gExpr :: Maybe ExprState -- ^ Expresión seleccionada.
                     , gTreeExpr :: Maybe TreeExpr -- ^ Árbol de una expresión.
                     , symCtrl :: TreeView   -- ^ La lista de símbolos para construir expresiones.
                     , axiomCtrl :: TreeView -- ^ La lista de axiomas para construir pruebas.
                     , gFaces :: Notebook -- ^ Las distintas caras de la interfaz.
                     , gUndo :: UndoList -- ^ Undo.
                     , gRedo :: RedoList -- ^ Redo.
                     , recentExprList :: RecentExprList -- ^ Lista de expresiones recientemente ingresadas.
                     , gStatistic :: Statistic -- ^ Conjunto de estadisticas.
                     , status :: StatusPlace  -- ^ La barra de estado.
                     , theorems :: [Theorem]
                     , undoing :: Bool
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
                             , expLabel :: Label -- ^ Label con el texto "Expresión:"
                             , formBox :: HBox   -- ^ Box donde se ingresa la formula
                             , clearButton :: Button -- ^ Botón para borrar toda la expresión.
                             , applyButton :: Button -- ^ Botón para aplicar la expresión.
                             , choicesButton :: Button -- ^ Botón para ver las expresiones que matchean en la prueba
                             }
