-- | Aspectos de la interfaz independientes de las expresiones.
module Equ.GUI.TypeTree where

import Equ.PreExpr
import Equ.Parser
import Equ.TypeChecker
import Equ.Types
import Equ.Rule
import Equ.Theories
import Equ.Proof hiding (goDownL, goDownR)

import Equ.GUI.Widget
import Equ.GUI.Types
import Equ.GUI.Utils
import Equ.GUI.Settings


import Graphics.UI.Gtk hiding (eventButton, eventSent,get)
import qualified Graphics.UI.Gtk as G
import Graphics.UI.Gtk.Gdk.EventM
import Graphics.UI.Gtk.Glade (GladeXML,xmlGetWidget)
import Data.Reference
import Data.Maybe(fromJust)

import Control.Monad.Trans(lift,liftIO)
import Control.Monad.State(get,evalStateT)
import Control.Monad(filterM) 
import Control.Arrow
import Data.Text(unpack)

import Data.List (deleteBy)
import qualified Data.Serialize as S
import qualified Data.ByteString as L
    

configEventSelectExprFromTree :: HBox -> GRef -> IO ()
configEventSelectExprFromTree b s = containerGetChildren b >>= \[eb] ->
                                    do eb `on` buttonPressEvent $ tryEvent $ 
                                          eventWithState (selectExprFromBox b) s
                                       return ()

-- Función principal que construye el arbol de tipado.
buildTypedFormTree :: ExprState -> IState ()
buildTypedFormTree te = get >>= \ s ->
                        getTreeExprBox >>= \ bTree -> 
                        cleanContainer bTree >>
                        setupEventExpr (fExpr te) (fType te) >>= 
                        \ (eb, tb) -> newBox >>= \ bb -> 
                        liftIO (configEventSelectExprFromTree eb s >>
                                configEventSelectTypeFromTree tb s >>
                                boxPackStart bb eb PackGrow 2 >>
                                boxPackStart bb tb PackGrow 2 >>
                                boxPackEnd bTree bb PackNatural 2 >>
                                widgetShowAll bb
                                ) >>
                        addExprToTree (fExpr te) (fType te) 
                                      (pathExpr te) eb tb >>
                        buildTypedFormTree' te bTree

-- | Función para construir un árbol de tipado. 
buildTypedFormTree' :: (BoxClass b) => ExprState -> b -> IState ()
buildTypedFormTree' te bTree = do
                    leftBranch <- goTypedExpr goDownL te
                    rightBranch <- goTypedExpr goDownR te
                    case (leftBranch, rightBranch) of
                        (Just (dlte, leb, ltb), Just (drte, reb, rtb)) -> 
                            newBox >>= \bTree' ->
                            liftIO (boxPackEnd bTree bTree' PackNatural 2) >>
                            fillNewBox bTree' reb rtb >>= \nVb ->
                            buildTypedFormTree' drte nVb >>
                            fillNewBox bTree' leb ltb >>= \nVb ->
                            buildTypedFormTree' dlte nVb
                        (Just (dlte, leb, ltb), Nothing) -> 
                            newBox >>= \bTree' ->
                            liftIO (boxPackEnd bTree bTree' PackNatural 2) >>
                            fillNewBox bTree' leb ltb >>= \nVb ->
                            buildTypedFormTree' dlte nVb
                        (Nothing, _) -> return ()
    where
        fillNewBox :: (BoxClass b) => b -> HBox -> HBox -> IState VBox
        fillNewBox bTree eb tb = get >>= \s ->newVBox >>= \nVb ->
                                 newBox >>= \nb -> 
                                 liftIO (
                                     boxPackStart nb eb PackGrow 2 >> 
                                     boxPackStart nb tb PackGrow 2 >> 
                                     boxPackEnd nVb nb PackGrow 2 >> 
                                     boxPackEnd bTree nVb PackGrow 2 >> 
                                     widgetShowAll bTree
                                 ) >>
                                 return nVb

configEventGeneralExpr :: EventBox -> HBox -> IO ()
configEventGeneralExpr eb b = 
                            onEvent enterNotifyEvent (highlightBox b hoverBg) >>
                            onEvent leaveNotifyEvent (unlightBox b genericBg) >>
                            return ()
    where onEvent event action = eb `on` event $ tryEvent action


configEventSelectTypeFromTree :: HBox -> GRef -> IO (ConnectId EventBox)
configEventSelectTypeFromTree b s = 
                        containerGetChildren b >>= \[tb'] ->
                        do
                        tb <- return $ castToEventBox tb'
                        tb `on` buttonPressEvent $ tryEvent $ 
                            eventWithState (
                                selectTypeFromBox b >>
                                getSelectExpr >>= \(Just te) ->
                                liftIO (entryNew) >>= \eText ->
                                liftIO (entrySetText eText (show (fType te)) >>
                                        containerRemove b tb >>
                                        boxPackStart b eText PackGrow 0 >> 
                                        widgetShowAll b) >>
                                configTypedEntry eText b tb te
                                        ) s

configTypedEntry :: Entry -> HBox -> EventBox -> ExprState -> IState ()
configTypedEntry eText b tb te = withState (onEntryActivate eText) 
                                      (liftIO (entryGetText eText) >>= 
                                       \text -> checkInType text >>= \checkText ->
                                       case checkText of
                                            Nothing -> return ()
                                            Just t -> 
                                                updateTypeSelectType te t >>
                                                updateTypedTypeFromTree te t >>
                                                liftIO (labelNew $ Just $ show t) >>= 
                                                \typeL -> 
                                                liftIO (containerGetChildren tb) >>= \[oldL] ->
                                                liftIO (containerRemove tb oldL) >> 
                                                liftIO (containerRemove b eText) >> 
                                                liftIO (set tb [containerChild := typeL]) >> 
                                                liftIO (set b [containerChild := tb] >> widgetShowAll b)
                                                >> return ()) >> 
                            return ()

configExprEntry :: Entry -> HBox -> ExprState -> IState ()
configExprEntry eText b te = withState (onEntryActivate eText) 
                                    (liftIO (entryGetText eText) >>= 
                                       \text -> checkInExpr text >>= \checkText ->
                                       case checkText of
                                            Nothing -> return ()
                                            Just e -> 
                                                updateExprSelectExpr te e >>
                                                liftIO (labelNew $ Just $ show e) >>= 
                                                \typeL -> 
                                                cleanTypedExprTree >>
                                                cleanTreeExpr >>
                                                getSelectExpr >>= \(Just te) ->
                                                buildTypedFormTree te >>
                                                return ()) >> 
                                return ()

-- | Aplica el type-checker a la expresión seleccionada.
typedCheckType :: IState ()
typedCheckType = getSelectExpr >>= \(Just te) ->
                 case checkPreExpr (toExpr $ fExpr te) of
                      Left err -> (reportErrWithErrPaned $ show err)
                      Right checkedType ->
                        case unify checkedType (fType te) emptySubst of
                          Left err' -> reportErrWithErrPaned $ show err'
                          Right _   -> reportSuccess "Los tipos coinciden."
                                      -- get >>= 
                                      -- liftIO . configEventCheckType (eventType te) checkedType

configEventCheckType :: HBox -> Type -> GRef -> IO ()
configEventCheckType b t s = labelNew (Just $ show t) >>= 
                             \typeL -> labelNew (Just $ "Vs") >>= 
                             \vsL -> eventBoxNew >>= \typeEb -> 
                             set typeEb [containerChild := typeL] >>
                             set b [containerChild := vsL] >>
                             set b [containerChild := typeEb] >>
                             highlightBox b errBg >> 
                             widgetShowAll b >>
                             (typeEb `on` buttonPressEvent $ tryEvent $ 
                                          eventWithState (
                                          liftIO (containerRemove b vsL >> 
                                                  containerRemove b typeEb >> 
                                                  widgetShowAll b)) s) >> 
                              return ()

checkInExpr :: String -> IState (Maybe PreExpr)
checkInExpr s = case parseFromString s of
                        Left err -> (reportErrWithErrPaned $ show err) >> return Nothing
                        Right expr -> return $ Just expr

checkInType :: String -> IState (Maybe Type)
checkInType s = case parseTyFromString s of
                     Left err -> reportErrWithErrPaned (show err) >> return Nothing
                     Right t -> return $ Just t

-- | Navega una expresión (la seleccionada) y devuelve, si se puede
-- hacer la navegación, una caja de tipado correspondiente con el nodo
-- al que llegamos.
goTypedExpr :: (Focus -> Maybe Focus) -> ExprState -> IState (Maybe (ExprState, HBox, HBox))
goTypedExpr go te = case (go . fExpr) te of
                Nothing -> return Nothing
                Just f -> get >>= \s -> setupEventExpr f TyUnknown >>= \(eb,tb) -> 
                         liftIO (configEventSelectExprFromTree eb s) >>
                         liftIO (configEventSelectTypeFromTree tb s) >>
                         addExprToTree f TyUnknown (fwd,bwd) eb tb >>= \ te' ->
                         return $ Just (te', eb, tb)
    where (fwd,bwd) = (fromJust . go . f, fromJust . go . b)
          (f,b) = pathExpr te

typedExprInEdit :: IState ()
typedExprInEdit = getSelectExpr >>= \(Just te) -> do
                    b <- return $ eventExpr te
                    [eb] <- liftIO $ containerGetChildren b
                    eText <- liftIO $ entryNew
                    liftIO (entrySetText eText (show (fst . fExpr $ te)) >>
                          containerRemove (castToBox b) eb >>
                          boxPackStart b eText PackGrow 0 >> 
                          widgetShowAll b)
                    configExprEntry eText b te

setupEventExpr :: Focus -> Type -> IState (HBox, HBox)
setupEventExpr (e,_) t = liftIO $ do
                                exprL <- labelNew $ Just $ show e
                                typeL <- labelNew $ Just $ show t
                                exprEb <- eventBoxNew
                                typeEb <- eventBoxNew
                                exprEbb <- hBoxNew False 0
                                typeEbb <- hBoxNew False 0
                                configEventGeneralExpr exprEb exprEbb
                                configEventGeneralExpr typeEb typeEbb
                                set exprEb [ containerChild := exprL ]
                                set typeEb [ containerChild := typeL ]
                                set exprEbb [ containerChild := exprEb ]
                                set typeEbb [ containerChild := typeEb ]
                                return (exprEbb, typeEbb)

-- | En base a una expresion seleccionada genera el arbol de tipado y abre
-- el respectivo panel.
typedExprTree :: IState ()
typedExprTree = getSelectExpr >>= \tse ->
                case tse of
                     Just se -> buildTypedFormTree se
                     Nothing -> reportErrWithErrPaned 
                                            "Ninguna expresion seleccionada."
