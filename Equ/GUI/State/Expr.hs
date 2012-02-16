module Equ.GUI.State.Expr where

import Equ.GUI.Types
import Equ.GUI.State.Internal hiding (local)
import Equ.GUI.State.Proof

import Equ.GUI.Utils
import Equ.Expr (Expr (..))
import Equ.Syntax (Variable)
import Equ.PreExpr (toExpr,goTop,Focus,PreExpr'(..),PreExpr)

import Equ.Proof(getStart, toProof)
import Equ.Proof(ProofFocus,ProofFocus',updateStartFocus,updateEndFocus,PM,validateProof,
                 toProof,goFirstLeft,updateMiddleFocus,goUp',getEndFocus,goRight,goEnd,goDownL',
                  getBasicFocus, validateProofFocus, goNextStep, goPrevStep)


import Graphics.UI.Gtk (HBox,ToggleButton,Image)

import Control.Monad.Reader
import Control.Arrow(first,(&&&))
import Data.Maybe
import qualified Data.Foldable as F


updateFocus' :: Focus -> GoBack -> GState -> GState
updateFocus' (e,p) (f,g) gst = case gExpr gst of
                                 Just gexpr -> gst { gExpr = Just $ upd gexpr }
                                 Nothing -> gst
    where upd gexpr = gexpr { fExpr = (e,p) }
                                        
                                        
-- | Actualiza el widget de expresión donde tenemos foco de entrada.                                        
updateExprWidget :: ExprWidget -> IState ()
updateExprWidget e = update (\gst -> case gExpr gst of
                                        Nothing -> gst
                                        Just es -> gst { gExpr = Just $ es {exprWidget = e
                                                                          , formCtrl = formBox e
                                                                          }})


getExprState :: IState (Maybe ExprState)
getExprState = getStatePartDbg "getExprState" gExpr

getExprWidget :: IState ExprWidget
getExprWidget = getStatePartDbg "getExprWidget" $ exprWidget . fromJust . gExpr

getExpr :: IState Focus
getExpr = getStatePartDbg "getExpr" $ fExpr . fromJust . gExpr

getFocusedExpr :: Move -> IState Focus
getFocusedExpr p = getExpr >>= return . p . goTop


getInitialExpr :: IState (Maybe Expr)
getInitialExpr = getProofState >>= \mps ->
                 case mps of
                    Nothing -> getExpr >>= return . Just . Expr . toExpr . goTop
                    Just ps -> either (return . (const  Nothing)) 
                                      (return . Just . Expr . toExpr . goTop) 
                                      (getStart $ toProof $ proof ps)

getFormBox :: IExpr' HBox
getFormBox = asks bx -- getExprWidget >>= return . formBox 

getEWidget :: IExpr' ExprWidget
getEWidget = asks ew

getTypeButton :: IExpr' ToggleButton
getTypeButton = asks ew >>= return . typeButton

getAnnotButton :: IExpr' ToggleButton
getAnnotButton = asks ew >>= return . annotButton

getImgStatus :: IExpr' Image
getImgStatus = asks ew >>= return . imgStatus

getPath :: IExpr' Move
getPath = asks mv

getProofMove :: IExpr' ProofMove
getProofMove = asks pme

localPath :: (Move -> Move) -> IExpr' a -> IExpr' a
localPath f = local (\env -> env { mv = f (mv env)})

localPathBox :: (Move -> Move) -> HBox -> IExpr' a -> IExpr' a
localPathBox f b = local (\env -> env { mv = f (mv env) , bx = b})

localBox :: HBox -> IExpr' a -> IExpr' a
localBox b = local (\env -> env { bx = b})

runEnv :: IExpr' a -> Env -> IState a
runEnv c env = runReaderT c env

runEnvBox :: IExpr' a -> (ExprWidget, Move, ProofMove) -> IState a
runEnvBox c (e,m,p) = runReaderT c (Env e m p (formBox e))

updateExprState :: ExprState -> IState ()
updateExprState es = update (\gst -> gst {gExpr = Just es}) >> showExpr


-- | Actualiza la expresión que se muestra en el área de estado;
-- esta es una función que puede dejar de tener sentido más adelante.
showExpr :: IState ()
showExpr = withRefValue $ uncurry putMsg . (status &&& show . toExpr . (fExpr . fromJust . gExpr) )


updateExpr'' :: Move -> (PreExpr -> PreExpr) -> GState -> GState
updateExpr'' g change gst = case (gProof gst,gExpr gst) of
                                  (Just gpr, Just gexpr) -> upd gpr gexpr 
                                  (Nothing, Just gexpr) ->  gst {gExpr = Just gexpr {fExpr = newExpr gexpr}} 
                                  (_,_) -> gst
    where upd gpr gexpr = gst { gProof = Just gpr' }
                -- Para actualizar la expresión dentro de la prueba, asumimos que el foco se encuentra
                -- en la prueba simple que deja a dicha expresión a la derecha.
                where  gpr' = gpr {proof = fromJust $ up (proof gpr) (newExpr gexpr)}
                       up pf f = let up1 = updateEndFocus (goFirstLeft pf) f in
                                    case goRight (fromJust up1) of
                                        Nothing -> Just $ goEnd (fromJust' up1)
                                        Just pf' -> Just $ goEnd $ goDownL' $ fromJust $ updateMiddleFocus (goUp' $ fromJust $ updateStartFocus pf' f) f
                       gexpr' = gexpr {fExpr = newExpr gexpr}
                       fromJust' = maybe (error "updateExpr'': up1 is Nothing") id
                     
          newExpr gexpr = first change . g . goTop . fExpr $ gexpr


-- -- | Devuelve la expresión que está enfocada en un momento dado.
getSelectedExpr :: IState Focus
getSelectedExpr = getProof >>= return . fromJust . getEndFocus
 
-- TODO: debemos hacer renombre si la variable está ligada?
-- | Actualización de la variable de cuantificación.
updateQVar :: Variable -> IState ()
updateQVar v = update (updateExpr'' id putVar) 
    where putVar (Quant q _ r t) = Quant q v r t
          putVar e = e

-- | Funcion que actualiza la expresion seleccionada por el usuario al mover el proofFocus.
updateSelectedExpr :: IState ()
updateSelectedExpr = getExprState >>= F.mapM_ 
                       (\es -> getProof >>= \ pf -> 
                              updateExprState (es {fExpr= fromJust $ getEndFocus pf }))
