-- | Manipulación de rehacer y deshacer acciones.
module Equ.GUI.Undo where

import Equ.GUI.Types
import Equ.GUI.State
import Equ.GUI.Utils
import Equ.GUI.Widget
import Equ.GUI.Expr
import Equ.GUI.Proof 

import Equ.PreExpr(toExpr)
import Equ.Proof

import Control.Monad.Reader
import qualified Data.Foldable as F (forM_)


undoEvent centralBox truthBox expr_w = 
    io (debug "Undo event") >>
    getUndoList >>= \ulist ->
        case ulist of
          [] -> io (debug "No hay pasos.") >> return ()
          [p] -> io (debug "No hay pasos previos.") >> return ()
          p':p:ps -> case urProof p of
                      Nothing -> F.forM_ (urExpr p) $ \f_expr -> 
                                undoAction (recreateExpr centralBox expr_w f_expr) p' p ps
                      Just pf -> undoAction (recreateProof pf centralBox truthBox expr_w) p' p ps
                                                        
          >>
          getUndoList >>= io . debug . ("UndoList es " ++) . show
                        
undoAction action p' p ps = setNoUndoing >>
                            action >>
                            updateUndoList (p:ps) >>
                            setUndoing >>
                            addToRedoList p'
                    

redoEvent centralBox truthBox expr_w = 
    io (debug "Redo event") >>
    getRedoList >>= \rlist ->
    case rlist of
      [] -> io (debug "lista redo vacia") >> return ()
      p:ps -> case (urProof p) of
               Nothing -> F.forM_ (urExpr p) $ \f_expr ->
                         redoAction (recreateExpr centralBox expr_w f_expr) p ps
               Just pf -> redoAction (recreateProof pf centralBox truthBox expr_w) p ps
                                                   
redoAction action p ps = setNoUndoing >>
                         action >>
                         updateRedoList ps >>
                         addToUndoListFromRedo p >>
                         setUndoing

-- TODO: Tiene sentido que estas funciones estén acá?
recreateProof pf cbox tbox expr_w = createNewProof (Just $ toProof pf) cbox tbox expr_w

recreateExpr cbox expr_w expr = removeAllChildren cbox >>
                              initExprState expr >>
                              runReaderT (reloadExpr (toExpr expr)) (expr_w,id,ProofMove $ Just)