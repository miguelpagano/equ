{-# Language Rank2Types, ExistentialQuantification, TypeSynonymInstances, MultiParamTypeClasses,
    ImpredicativeTypes #-}
module Equ.GUI.Types where

import Equ.PreExpr
import Equ.Exercise

import Equ.Proof (Proof,PM,ProofFocus,Theorem,Hypothesis,Proof',ProofFocus')
import Equ.Proof.Proof (Ctx,Proof'(..))
import Equ.Proof.ListedProof
import Equ.Rule(Relation)

import Graphics.UI.Gtk ( WidgetClass, Statusbar, ContextId, HBox, TreeView
                       , EventBox, Label, Button, Notebook, HPaned, IconView
                       , Window, Image, ToggleButton, ComboBox, ListStore
                       , GObjectClass, ConnectId, VBox
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
data URMove = URMove { urProof :: Maybe ListedProof -- ^ Si guardamos una prueba. 
                     , urExpr :: Maybe Focus
                     }
instance Show URMove where
    show u = show (urProof u,urExpr u)

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

data ProofState = ProofState { proof :: ListedProof   -- ^ La prueba que estamos construyendo
                             , proofWidget :: ListedProofWidget -- ^ navegacion de la interfaz
                             , validProof :: PM Proof
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
                             , exprEventsIds :: [Connectable]
                             , exprProofIndex :: Int    -- ^ Indice dentro de la prueba, correspondiente al paso en el que se encuentra a la derecha.
                             , ewId :: String
                             }

instance Show ExprWidget where
    show e = "EWidget- id="++ewId e
                             
                             
-- WIDGET PARA PRUEBAS
-- Estructura de cajas:
{- centerBox -> stepBox -> eventBoxAxiom -> axiomWidget -}


data ProofStepWidget = ProofStepWidget {
                        relation :: (ComboBox,ListStore Relation)
                      , axiomWidget :: HBox
                      , eventBoxAxiom :: EventBox
                      , addStepButton :: Button
                      , validImage :: Image
                      , stepBox :: HBox
                      , centerBox :: VBox
                      , stepEventsIds :: [Connectable]
                      , stepProofIndex :: Int  -- ^ Indice del paso dentro de la prueba.
                      , pswId :: String
                      }

type ProofWidget = Proof' () () ProofStepWidget ExprWidget

instance Show ProofWidget where
    show (Simple _ _ e1 e2 step) = "PWidget- Ei -> id=" ++ ewId e1 ++ ", ind=" ++ show (exprProofIndex e1) ++
                                   ", E2 -> id=" ++ ewId e2 ++ ", ind=" ++ show (exprProofIndex e2) ++
                                   ", STEP -> id=" ++ pswId step ++", ind=" ++ show (stepProofIndex step)
    show _ = ""

type ListedProofWidget = ListedProof' () () ProofStepWidget ExprWidget

instance Show ListedProofWidget where
    show lProof = show (pList lProof) ++ " | index: " ++ show (selIndex lProof)

type IExpr a = Move -> IState a

type Env = (ExprWidget,Move,Int)

type IExpr' a = ReaderT (ExprWidget,Move,Int) IState a

-- tipo para poder crear lista heterogénea de objetos conectables a una señal.
data Connectable = forall w . GObjectClass w => Connectable (ConnectId w)


-- newtype ProofMove = ProofMove { pm ::  forall ctxTy relTy proofTy exprTy . ProofFocus' ctxTy relTy proofTy exprTy -> 
--                                       Maybe (ProofFocus' ctxTy relTy proofTy exprTy)}


data ExprStatus =  Unknown | Parsed | NotParsed | TypeChecked



