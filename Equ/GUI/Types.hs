{-# Language Rank2Types, ExistentialQuantification, TypeSynonymInstances, MultiParamTypeClasses,
    ImpredicativeTypes #-}
module Equ.GUI.Types where

import Equ.PreExpr
import Equ.Exercise

import Equ.Proof (Proof,PM,ProofFocus,Theorem,Hypothesis,Proof',ProofFocus')
import Equ.Proof.Proof (Ctx)
import Equ.Rule(Relation)

import Graphics.UI.Gtk ( WidgetClass, Statusbar, ContextId, HBox, TreeView
                       , EventBox, Label, Button, Notebook, HPaned, IconView
                       , Window, Image, ToggleButton, ComboBox, ListStore
                       )

import Equ.Types

import Control.Monad.State.Strict
import Control.Monad.Reader
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
                     , gExercise :: Maybe Exercise -- ^ El estado de la edición de un ejercicio.
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
                           , fType :: Type  -- (Manu) Para qué usamos esto?
                           , eventType :: HBox  -- (Manu) Para qué usamos esto?
                           , exprWidget :: ExprWidget
                           , formCtrl :: HBox -- Caja de la subexpresión que se está editando. Deberia cumplirse el invariante de que
                                              -- formCtrl es hijo de (formBox exprWidget)
                           }

data ProofState = ProofState { proof :: ProofFocus   -- ^ La prueba que estamos construyendo
                             , validProof :: PM Proof
                             , axiomBox :: HBox -- ^ El contenedor para mostrar el axioma aplicado
                             , proofWidget :: ProofFocusWidget -- ^ Focus para navegar la interfaz de prueba
                             }

type GRef = IORef GState
type IState = StateT GRef IO
type IRG = IState () 

data WExpr w = WExpr { widget :: WidgetClass w => w
                     , wexpr :: PreExpr
                     }

instance Reference IORef IState where
    readRef = liftIO . readRef
    writeRef r = liftIO . writeRef r
    newRef = liftIO . newRef

    
-- WIDGET PARA EXPRESIONES
data ExprWidget = ExprWidget { extBox :: HBox       -- ^ Widget más externo.
                             , formBox :: HBox      -- ^ Box donde se ingresa la formula
                             , choicesButton :: Maybe Button -- ^ Botón para ver las expresiones que matchean 
                                                            -- en la prueba (la expresion inicial no lo tiene).
                             , annotButton :: ToggleButton -- ^ Botón para anotaciones.
                             , typeButton  :: ToggleButton -- ^ Botón para árbol de tipado.
                             , imgStatus   :: Image      -- ^ Imagen para estado.
                             }

                             
-- WIDGET PARA PRUEBAS
data ProofStepWidget = ProofStepWidget {
                        relation :: (ComboBox,ListStore Relation)
                      , axiomWidget :: HBox
                      , eventBoxAxiom :: EventBox
                      , addStepButton :: Button
                      , validImage :: Image
                      , stepBox :: HBox
                      -- ids de los manejadores de eventos click izquierdo y derecho sobre la caja de axioma:
                      --, eventsId :: (ConnectId EventBox,ConnectId EventBox) 
                      }

type ProofWidget = Proof' () () ProofStepWidget ExprWidget

type ProofFocusWidget = ProofFocus' () () ProofStepWidget ExprWidget

type IExpr a = Move -> IState a

type Env = (ExprWidget,Move,ProofMove)

type IExpr' a = ReaderT (ExprWidget,Move,ProofMove) IState a

newtype ProofMove = ProofMove { pm ::  forall ctxTy relTy proofTy exprTy . ProofFocus' ctxTy relTy proofTy exprTy -> 
                                      Maybe (ProofFocus' ctxTy relTy proofTy exprTy)}


data ExprStatus =  Unknown | Parsed | NotParsed | TypeChecked
