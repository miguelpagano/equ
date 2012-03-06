{-# Language Rank2Types, ExistentialQuantification, TypeSynonymInstances, MultiParamTypeClasses,
    ImpredicativeTypes #-}
module Equ.GUI.Types where

import Equ.PreExpr
import Equ.Exercise

import Equ.Proof (Proof,PM,ProofFocus,Theorem,Hypothesis,Proof',ProofFocus')
import Equ.Proof.Proof (Ctx,Proof'(..))
import Equ.Proof.ListedProof
import Equ.Proof.Annot
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
                     , symStore :: ListStore SynItem
                     , symCid   :: Maybe (ConnectId IconView)
                     , axiomCtrl :: TreeView -- ^ La lista de axiomas para construir pruebas.
                     , gExercise :: Maybe Exercise -- ^ El estado de la edición de un ejercicio.
                     , gUndo :: UndoList -- ^ Undo.
                     , gRedo :: RedoList -- ^ Redo.
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
                             , proofAnnots :: ListedAnnots
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

data Env = Env { ew :: ExprWidget
               , mv :: Move
               , pme :: Int
               , bx :: HBox
               }

type IExpr' a = ReaderT Env  IState a
type SynItem = (String, HBox -> IExpr' ())

-- tipo para poder crear lista heterogénea de objetos conectables a una señal.
data Connectable = forall w . GObjectClass w => Connectable (ConnectId w)

data ExprStatus =  Unknown | Parsed | NotParsed | TypeChecked

instance Show ExprStatus where
    show Unknown = "Ninguna info relevante."
    show Parsed = "Parseado exitoso. Sin tipado."
    show NotParsed = "No parseado."
    show TypeChecked = "Parseado y tipado exitosos."

