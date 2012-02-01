module Equ.GUI.State.Expr where

import Equ.GUI.Types

import Graphics.UI.Gtk (HBox,ToggleButton)

import Control.Monad.Reader
import Control.Arrow((***))

getExprWidget :: IExpr' ExprWidget
getExprWidget = asks fst

getFormBox :: IExpr' HBox
getFormBox = asks (formBox . fst)

getTypeButton :: IExpr' ToggleButton
getTypeButton = asks (typeButton . fst)

getAnnotButton :: IExpr' ToggleButton
getAnnotButton = asks (annotButton . fst)

getPath :: IExpr' Move
getPath = asks snd

localPath :: (Move -> Move) -> IExpr' a -> IExpr' a
localPath f = local (id *** f)