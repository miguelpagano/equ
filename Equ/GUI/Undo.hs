module Equ.GUI.Undo where

import Equ.GUI.Types
import Equ.GUI.State
import Equ.GUI.Utils
import Equ.GUI.Widget
import Equ.GUI.Settings
import Equ.GUI.Expr
import Equ.GUI.SymbolList
import Equ.GUI.TruthList
import Equ.GUI.Proof 
import Equ.GUI.TypeTree
import Equ.GUI.Truth

import Equ.PreExpr(toFocus, toFocuses, agrupOp, agrupNotOp, opOfFocus, 
                   holePreExpr,PreExpr, toExpr, emptyExpr)
import Equ.Proof
import Equ.Parser
import Equ.Theories

import Equ.Rule (relEq,relEquiv)

import qualified Graphics.UI.Gtk as G
import Graphics.UI.Gtk hiding (eventButton, eventSent,get)
import Graphics.UI.Gtk.Gdk.Events 
import Graphics.UI.Gtk.Glade
import Data.Text (pack,unpack)

import Data.Reference

import Control.Monad.State (evalStateT,get)
import Control.Monad(liftM, when)
import Control.Monad.Trans(liftIO)

import qualified Data.Foldable as F (forM_)

import Data.Map (fromList)


undoEvent centralBox truthBox exprBox = 
    io (debug "Undo event") >>
    getUndoList >>= \ulist ->
        case ulist of
          [] -> io (debug "No hay pasos.") >> return ()
          [p] -> io (debug "No hay pasos previos.") >> return ()
          p':p:ps -> case urProof p of
                      Nothing -> F.forM_ (urExpr p) $ \f_expr -> 
                                undoAction (recreateExpr centralBox exprBox f_expr) p' p ps
                      Just pf -> undoAction (recreateProof pf centralBox truthBox exprBox) p' p ps
                                                        
          >>
          getUndoList >>= io . debug . ("UndoList es " ++) . show
                        
undoAction action p' p ps = setNoUndoing >>
                            action >>
                            updateUndoList (p:ps) >>
                            setUndoing >>
                            addToRedoList p'
                    

redoEvent centralBox truthBox exprBox = 
    io (debug "Redo event") >>
    getRedoList >>= \rlist ->
    case rlist of
      [] -> liftIO (debug "lista redo vacia") >> return ()
      p:ps -> case (urProof p) of
               Nothing -> F.forM_ (urExpr p) $ \f_expr ->
                         redoAction (recreateExpr centralBox exprBox f_expr) p ps
               Just pf -> redoAction (recreateProof pf centralBox truthBox exprBox) p ps
                                                   
redoAction action p ps = setNoUndoing >>
                         action >>
                         updateRedoList ps >>
                         addToUndoListFromRedo p >>
                         setUndoing

recreateProof pf cbox tbox ebox = createNewProof (Just $ toProof pf) cbox tbox ebox

recreateExpr cbox ebox expr = removeAllChildren cbox >>
                                      initExprState expr >>
                                      reloadExpr ebox (toExpr expr)