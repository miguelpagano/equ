
module Equ.GUI.State.Expr where

import Equ.GUI.Types
import Equ.GUI.State.Internal hiding (local)
import Equ.GUI.State.Proof

import Equ.GUI.Utils
import Equ.Expr (Expr (..))
import Equ.Syntax (Variable)
import Equ.PreExpr (toExpr,goTop,Focus,PreExpr'(..),PreExpr,toFocus,holePreExpr)

import Equ.Proof(getStart, toProof,getEnd,getRel)
import Equ.Proof.ListedProof

import Graphics.UI.Gtk (HBox,ToggleButton,Image, castToHBox,Widget)

import Control.Monad.Reader
import Control.Arrow(first,(&&&))
import Data.Maybe
import Data.List(find)
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

-- Funcion para obtener el widget de expresion seleccionada en la prueba:
getExprWidget :: IState ExprWidget
getExprWidget = getProofState >>= \ps ->
                case ps of
                     Nothing -> getStatePartDbg "getExprWidget" $ exprWidget . fromJust . gExpr
                     Just ps' -> return $ getSelExpr (proofWidget ps')

getExpr :: IState Focus
getExpr = getProofState >>= \ps ->
          case ps of
               Nothing -> getStatePartDbg "getExpr" $ 
                          (\g -> case gExpr g of
                                    Nothing -> toFocus holePreExpr
                                    Just es -> fExpr es)
               Just ps' -> return $ getSelExpr $ proof ps'

getFocusedExpr :: Move -> IState Focus
getFocusedExpr p = getExpr >>= return . p . goTop

getInitialFocus :: IState (Maybe Focus)
getInitialFocus = getInitialExpr >>= \initExpr ->
                  case initExpr of
                      Nothing -> return Nothing
                      Just (Expr e) -> return $ Just $ toFocus e

getInitialExpr :: IState (Maybe Expr)
getInitialExpr = getProofState >>= \mps ->
                 case mps of
                    Nothing -> getExpr >>= return . Just . Expr . toExpr . goTop
                    Just ps -> either (return . (const  Nothing)) 
                                      (return . Just . Expr . toExpr) 
                                      (getStart $ toProof $ pFocus $ proof ps)

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

getProofMove :: IExpr' Int
getProofMove = asks pme

localPath :: (Move -> Move) -> IExpr' a -> IExpr' a
localPath f = local (\env -> env { mv = f (mv env)})

localPathBox :: (Move -> Move) -> HBox -> IExpr' a -> IExpr' a
localPathBox f b = local (\env -> env { mv = f (mv env) , bx = b})

localBox :: HBox -> IExpr' a -> IExpr' a
localBox b = local (\env -> env { bx = b})

runEnv :: IExpr' a -> Env -> IState a
runEnv c env = runReaderT c env

runEnvBox :: IExpr' a -> (ExprWidget, Move, Int) -> IState a
runEnvBox c (e,m,p) = runReaderT c (Env e m p (formBox e))

updateExprState :: ExprState -> IState ()
updateExprState es = update (\gst -> gst {gExpr = Just es}) >> showExpr

-- | Actualiza la expresión que se muestra en el área de estado;
-- esta es una función que puede dejar de tener sentido más adelante.
showExpr :: IState ()
showExpr = 
    getExprState >>= \es ->
    case es of
        Nothing -> return ()
        Just es' -> withRefValue $ uncurry putMsg . 
                        (status &&& show . toExpr . (fExpr . fromJust . gExpr))

updateExpr'' :: Move -> (PreExpr -> PreExpr) -> GState -> GState
updateExpr'' g change gst = 
    case (gProof gst,gExpr gst) of
        (Just gpr, _) -> upd gpr 
        (Nothing, Just gexpr) -> gst {gExpr =Just gexpr {fExpr = newExpr gexpr}} 
        (_,_) -> gst
    where upd gpr = gst { gProof = Just gpr' }
            -- Para actualizar la expresión dentro de la prueba, asumimos que el foco se encuentra
            -- en la prueba simple que deja a dicha expresión a la derecha.
            where  gpr' = gpr {proof = updateSelExpr (newExpr' gpr) (proof gpr)}
                       --gexpr' = gexpr {fExpr = newExpr gexpr}
               
          newExpr gexpr = first change . g . goTop . fExpr $ gexpr
          newExpr' gpr = let fexpr = getSelExpr (proof gpr) in
                        first change . g . goTop $ fexpr
              
updateExpr' :: PreExpr -> Move -> GState -> GState
updateExpr' e p = updateExpr'' p (const e)

-- -- | Devuelve la expresión que está enfocada en un momento dado.
getSelectedExpr :: IState Focus
getSelectedExpr = getProof >>= return . getSelExpr
 
-- TODO: debemos hacer renombre si la variable está ligada?
-- | Actualización de la variable de cuantificación.
updateQVar v p = update (updateExpr'' p putVar) 
    where putVar (Quant q _ r t) = Quant q v r t
          putVar e = e

-- | Funcion que actualiza la expresion seleccionada por el usuario al mover el proofFocus.
updateSelectedExpr :: IState ()
updateSelectedExpr = getExprState >>= F.mapM_ 
                       (\es -> getProof >>= \ lp -> 
                              updateExprState (es {fExpr= getSelExpr lp }))

-- | En base a un modo de vista retorna la caja.
takeBox :: ViewMask -> WExprList -> Widget
takeBox vmask wes = case vmask of
                        Sugar -> bestBox wes
                        Kernel -> kernelBox wes

-- | Retorna la caja sin sugar.
kernelBox :: WExprList -> Widget
kernelBox = wKernel . head . weList

-- | Retorna la caja que mejor represente a un focus. Donde con mejor represente
-- nos referimos a la caja con Sugar.
bestBox :: WExprList -> Widget
bestBox wes = maybe (wKernel $ head $ weList wes) id (ws wes)
    where
        ws :: WExprList -> Maybe Widget
        ws = wSugar . head . weList

-- | En base a un focus retorna la caja, sin Sugar, correspondiente en la prueba.
findExprKernelBox :: Focus -> ExprWidget -> IState HBox
findExprKernelBox = findExprBox' (\f -> \we -> (wExpr we) == f) (castToHBox . wKernel)

-- | En base a un path retorna la caja correspondiente en la prueba.
findPathBox :: Focus -> ExprWidget -> IState HBox
findPathBox = findExprBox' (\f -> \we -> (snd $ wExpr we) == snd f) (castToHBox . best)
    where
        best :: WExpr -> Widget
        best we = maybe (wKernel we) id (wSugar we)

-- | En base a un focus retorna la caja correspondiente en la prueba.
findExprBox :: Focus -> ExprWidget -> IState HBox
findExprBox = findExprBox' (\f -> \we -> (wExpr we) == f) (castToHBox . best)
    where
        best :: WExpr -> Widget
        best we = maybe (wKernel we) id (wSugar we)

-- Función auxiliar para encontrar la caja correspondiente a un focus.
findExprBox' :: (Focus -> WExpr -> Bool) -> (WExpr -> HBox) -> Focus -> ExprWidget -> 
                IState HBox
findExprBox' condition func f ew = 
                        case find (condition f) $ weList $ wExprL ew of
                            Nothing -> io (debug $ "finExprBox: Nothing!") >> 
                                       return (formBox ew)
                            Just we -> (return . func) we

-- | Dado un focus y un exprWidget(correspondiente a este focus en la prueba)
-- retorna si esta escrito con Sugar o no.
focusHasSugar :: Focus -> ExprWidget -> IState Bool
focusHasSugar f ew = case find (\we -> (wExpr we) == f) $ weList $ wExprL ew of
                        Nothing -> io (debug $ "focusHasSugar: Nothing!") >> 
                                      return False
                        Just we -> return $ hasSugar we
    where
        hasSugar :: WExpr -> Bool
        hasSugar we = maybe False (const True) (wSugar we)

-- | Lista vacia.
emptyWExprList :: WExprList
emptyWExprList = WExprList [] Nothing

-- | Agrega un WExpr a la lista.
appendWExprList :: WExpr -> WExprList -> WExprList
appendWExprList we wes = WExprList (we: weList wes) $ weMarked wes

-- TODO: Tiene un detalle importante. Que pasa si hacemos concat de listas que
-- tiene cajas con markup. Deberíamos borrar el markup de las cajas, poner
-- Nothing y listo. De momento no lo hago :D Acomodar!
concatWExprList :: WExprList -> WExprList -> WExprList
concatWExprList wes wes' = WExprList (weList wes ++ weList wes') Nothing

-- | Obtiene la caja que tiene el focus de re-escritura, si no, Nothing.
getFocusBox :: ExprWidget -> Maybe HBox
getFocusBox ew = case weMarked $ wExprL ew of
                  Nothing -> Nothing
                  Just wem -> return $ castToHBox $ best wem
    where
        best :: WExpr -> Widget
        best we = maybe (wKernel we) id (wSugar we)

-- | Hace un update de la caja que tiene el focus de re-escritura.
-- Es decir, que tiene el subrayado de la expresión que se re-escribio,
-- al aplicar un axioma exitosamente.
updateFocusBoxExprWidget :: Widget -> ExprWidget -> IState ()
updateFocusBoxExprWidget b ew = do 
                    lpw <- getProofWidget
                    uew <- updateW ew
                    ulpw <- updateE uew lpw
                    updateProofWidget ulpw
    where
        updateE :: ExprWidget -> ListedProofWidget -> IState ListedProofWidget
        updateE uew lpw =  do
                    i <- return $ selIndex lpw
                    if i == 0 then
                        return $ updateFirstExpr uew lpw
                    else
                        return $ updateExprAt (i-1) uew lpw
        updateW :: ExprWidget -> IState ExprWidget
        updateW ew = 
            case find (\we -> ((wSugar we) == (Just b)) || (wKernel we == b)) $ 
                        weList $ wExprL ew of
                Nothing -> io (debug $ "updateFocusBoxExprWidget: Nothing!") >>
                           return ew
                Just we -> return $ ew {wExprL = (wExprL ew) {weMarked = Just we}}
