module Equ.GUI.State.Expr where

import Equ.GUI.Types
import Equ.GUI.State hiding (getExprWidget)

import Equ.Expr (Expr (..))
import Equ.PreExpr (toExpr)
import Equ.Proof(getStart, toProof)
import Equ.Proof.ListedProof

import Graphics.UI.Gtk (HBox,ToggleButton,Image)

import Control.Monad.Reader

getInitialExpr :: IState (Maybe Expr)
getInitialExpr = getProofState >>= \mps ->
                 case mps of
                    Nothing -> getExpr >>= return . Just . Expr . fst
                    Just ps -> either (return . (const  Nothing)) 
                                      (return . Just . Expr . toExpr) 
                                      (getStart $ toProof $ pFocus $ proof ps)

getExprWidget :: IExpr' ExprWidget
getExprWidget = asks (\(e,_,_) -> e)

getFormBox :: IExpr' HBox
getFormBox = getExprWidget >>= return . formBox 

getTypeButton :: IExpr' ToggleButton
getTypeButton = getExprWidget >>= return . typeButton

getAnnotButton :: IExpr' ToggleButton
getAnnotButton = getExprWidget >>= return . annotButton

getImgStatus :: IExpr' Image
getImgStatus = getExprWidget >>= return . imgStatus

getPath :: IExpr' Move
getPath = asks (\(_,p,_) -> p)

getProofMove :: IExpr' Int
getProofMove = asks (\(_,_,pm) -> pm) 

localPath :: (Move -> Move) -> IExpr' a -> IExpr' a
localPath f = local (\(e,p,m) -> (e,f p,m))