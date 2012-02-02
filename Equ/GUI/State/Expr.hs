module Equ.GUI.State.Expr where

import Equ.GUI.Types

import Graphics.UI.Gtk (HBox,ToggleButton,Image)

import Control.Monad.Reader

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

getProofMove :: IExpr' ProofMove
getProofMove = asks (\(_,_,pm) -> pm) 

localPath :: (Move -> Move) -> IExpr' a -> IExpr' a
localPath f = local (\(e,p,m) -> (e,f p,m))