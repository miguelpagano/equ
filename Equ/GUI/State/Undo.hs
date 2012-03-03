{-# Language OverloadedStrings #-}
-- | Utilidades varias que tienen que ver con el estado de la
-- interfaz (es probable que se muden a Equ.GUI.State) y con
-- funciones convenientes que podrían mudarse a otros módulos.
module Equ.GUI.State.Undo where

import Equ.GUI.Types
import Equ.GUI.State.Internal hiding (local)
import Equ.GUI.State.Proof
import Equ.GUI.State.Expr

import Equ.GUI.Utils

import Control.Monad(when)
import qualified Data.Foldable as F

getUndoList :: IState UndoList
getUndoList = getStatePart gUndo

getRedoList :: IState RedoList
getRedoList = getStatePart gRedo
 
getUndoing :: IState Bool
getUndoing = getStatePart undoing


cleanRedoList :: IRG
cleanRedoList = update $ \gst -> gst { gRedo = [] }

setUndoing :: IRG
setUndoing = update $ \gst -> gst { undoing = True }

setNoUndoing :: IRG
setNoUndoing = update $ \gst -> gst { undoing = False }

updateUndoList :: UndoList -> IRG
updateUndoList ulist = update $ \gst -> gst { gUndo = ulist }
                                 
                                 
addToUndoList :: IRG
addToUndoList = getProofState >>= \ps ->
                    case ps of
                         Nothing -> getExprState >>= \es ->
                            F.forM_ es $ \es ->
                                getExpr >>= \e ->
                                addURMove (urmove (Nothing,Just e))
                         Just ps -> getProof >>= \p ->
                                    addURMove (urmove (Just p,Nothing))
                
    where addURMove urm= getUndoing >>= \u -> when u $
                            getUndoList >>= \ulist ->
                            updateUndoList (urm:ulist) >>
                            getUndoList >>= \ulist' ->
                            io (debug $ "addToUndoList. UndoList es " ++ show ulist') >>
                            cleanRedoList
          urmove (proof,expr) = URMove { urProof = proof
                                       , urExpr = expr}          
             
addToUndoListFromRedo :: URMove -> IRG
addToUndoListFromRedo m = getUndoList >>= \ulist ->
                          updateUndoList (m:ulist)
             
updateRedoList :: RedoList -> IRG
updateRedoList rlist = update $ \gst -> gst { gRedo = rlist }
             
addToRedoList :: URMove -> IRG
addToRedoList m = getRedoList >>= \rlist ->
                  updateRedoList (m:rlist)
