-- | Aspectos de la interfaz independientes de las expresiones.
module Equ.GUI.TypeTree where

import Equ.PreExpr
import Equ.Syntax
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
import Control.Monad(filterM, when, unless) 
import Control.Arrow
import Data.Text(unpack)

import Data.List (deleteBy)
import qualified Data.Serialize as S
import qualified Data.ByteString as L

-- Función principal que construye el arbol de tipado.
buildTreeExpr :: ExprState -> IState ()
buildTreeExpr te = 
                get >>= \ s ->
                getTreeExprBox >>= \ bTreeExpr -> 
                getTreeOpBox >>= \bTreeOp ->
                cleanContainer bTreeExpr >>
                cleanContainer bTreeOp >>
                setupEventExpr (fExpr te) (fType te) >>= 
                \(eb, tb) -> newBox >>= \ bb -> 
                addMainExprToTree (fExpr te) (fType te) (pathExpr te) eb tb >>= \te ->
                liftIO (configEventSelectTypeFromTree tb s >>
                        boxPackStart bb eb PackGrow 2 >>
                        boxPackStart bb tb PackGrow 2 >>
                        boxPackEnd bTreeExpr bb PackNatural 2 >>
                        widgetShowAll bb
                        ) >>
                buildTreeExpr' te bTreeExpr >>
                updateOpExprTree (agrupOp $ toFocusesWithGo $ fst $ fExpr te)
                                    Nothing Nothing >>
                buildTreeOpList bTreeOp

-- Función secundaria que contruye el árbol de tipado.
buildTreeExpr' :: (BoxClass b) => ExprState -> b -> IState ()
buildTreeExpr' te bTree = do
                    leftBranch <- goTypedExpr goDownL te
                    rightBranch <- goTypedExpr goDownR te
                    case (leftBranch, rightBranch) of
                        (Just (dlte, leb, ltb), Just (drte, reb, rtb)) -> 
                            newBox >>= \bTree' ->
                            liftIO (boxPackEnd bTree bTree' PackNatural 2) >>
                            fillNewBox bTree' reb rtb drte >>= \nVb ->
                            when ((checkIsAtom . fExpr) dlte) 
                                    (addNotOpExprTree dlte) >>
                            buildTreeExpr' drte nVb >>
                            fillNewBox bTree' leb ltb dlte >>= \nVb ->
                            when ((checkIsAtom . fExpr) drte) 
                                    (addNotOpExprTree drte) >>
                            buildTreeExpr' dlte nVb
                        (Just (dlte, leb, ltb), Nothing) -> 
                            newBox >>= \bTree' ->
                            liftIO (boxPackEnd bTree bTree' PackNatural 2) >>
                            fillNewBox bTree' leb ltb dlte >>= \nVb ->
                            when ((checkIsAtom . fExpr) dlte) 
                                    (addNotOpExprTree dlte) >>
                            buildTreeExpr' dlte nVb
                        (Nothing, _) -> return ()
    where
        fillNewBox :: (BoxClass b) => b -> HBox -> HBox -> ExprState -> IState VBox
        fillNewBox bTree eb tb te = get >>= \s -> newVBox >>= \nVb ->
                                 newBox >>= \nb -> 
                                 liftIO (
                                     boxPackStart nb eb PackGrow 2 >> 
                                     when ((checkIsAtom . fExpr) te) 
                                           (boxPackStart nb tb PackGrow 2) >> 
                                     boxPackEnd nVb nb PackGrow 2 >> 
                                     boxPackEnd bTree nVb PackGrow 2 >> 
                                     widgetShowAll bTree
                                 ) >>
                                 return nVb

-- Construye la lista de operadores.
buildTreeOpList :: VBox -> IState ()
buildTreeOpList b = get >>= \s -> getOpExprTree >>= \fs -> liftIO $ build fs b s
    where 
        t :: (Focus, Move) -> Type
        t f = tType $ fromJust $ opOfFocus f
        build :: [[(Focus, Move)]] -> VBox -> GRef -> IO () 
        build [] b s = widgetShowAll b
        build ((f:fs):fss) b s = 
                            do
                            typeL <- labelNew $ Just $ 
                                        show $ t f
                            typeEb <- eventBoxNew
                            typeEbb <- hBoxNew False 0
                            set typeL [miscXalign := 0.005]
                            configEventGeneralExpr typeEb typeEbb
                            set typeEb [ containerChild := typeL ]
                            boxPackStart typeEbb typeEb PackGrow 0
                            configEventInTypeForOp (f:fs) typeEbb s
                            exprL <- labelNew $ Just $ 
                                        show (fromJust $ opOfFocus f) ++ " : "
                            set exprL [miscXalign := 0.005]
                            exprEb <- eventBoxNew
                            exprEbb <- hBoxNew False 0
                            set exprEb [ containerChild := exprL ]
                            boxPackStart exprEbb exprEb PackNatural 0
                            b' <- hBoxNew False 0
                            boxPackStart b' exprEbb PackNatural 0
                            set b' [ containerChild := typeEbb ]
                            set b [ containerChild := b' ]
                            build fss b s

-- Configura la acción de ingresar un tipo para un operador.
configEventInTypeForOp :: [(Focus, Move)] -> HBox -> GRef -> IO (ConnectId EventBox)
configEventInTypeForOp (f:fs) b s = 
                        containerGetChildren b >>= \[tb'] ->
                        do
                        tb <- return $ castToEventBox tb'
                        tb `on` buttonPressEvent $ tryEvent $ 
                            eventWithState (
                                liftIO (containerGetChildren (castToEventBox tb')) >>= \[l] ->
                                liftIO (entryNew) >>= \eText ->
                                liftIO (labelGetLabel (castToLabel l)) >>= \textL ->
                                liftIO (entrySetText eText textL >>
                                        containerRemove b tb >>
                                        boxPackStart b eText PackGrow 0 >> 
                                        widgetShowAll b) >>
                                configTypeOpEntry (f:fs) eText b tb) s

-- Configura la acción de checkeo del tipo ingresado para un operador.
configTypeOpEntry :: [(Focus, Move)] -> Entry -> HBox -> EventBox -> IState ()
configTypeOpEntry fs eText b tb = 
                withState (onEntryActivate eText) 
                (liftIO (entryGetText eText) >>= 
                \text -> checkInType text >>= \checkText ->
                case checkText of
                    Nothing -> return ()
                    Just t -> 
                        updateTypeOpInMainExprTree fs t >>
                        getOpExprTree >>= \fss ->
                        updateOpExprTree fss (Just fs) (Just t) >>
                        liftIO (labelNew $ Just $ show t) >>= 
                        \typeL -> 
                        liftIO (set typeL [miscXalign := 0.005]) >>
                        liftIO (containerGetChildren tb) >>= \[oldL] ->
                        liftIO (containerRemove tb oldL) >> 
                        liftIO (containerRemove b eText) >> 
                        liftIO (set tb [containerChild := typeL]) >> 
                        liftIO (set b [containerChild := tb] >> widgetShowAll b)
                        >> return ()) >> 
                return ()

-- Configuración general para los botones. 
-- (Coloreo y desColoreo al pasar por encima)
configEventGeneralExpr :: (BoxClass w) => EventBox -> w -> IO ()
configEventGeneralExpr eb b = 
                            onEvent enterNotifyEvent (highlightBox b hoverBg) >>
                            onEvent leaveNotifyEvent (unlightBox b genericBg) >>
                            return ()
    where onEvent event action = eb `on` event $ tryEvent action

-- Configura la acción de ingresar un tipo para la expresión principal del 
-- árbol de tipado o para sus hojas(atomos).
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

-- Configura la acción de checkeo del tipo ingresado para la expresión principal
-- del árbol de tipado o para sus hojas.
configTypedEntry :: Entry -> HBox -> EventBox -> ExprState -> IState ()
configTypedEntry eText b tb te = 
                withState (onEntryActivate eText) 
                (liftIO (entryGetText eText) >>= 
                \text -> checkInType text >>= \checkText ->
                case checkText of
                    Nothing -> return ()
                    Just t -> 
                        when ((checkIsAtom . fExpr) te) 
                             (updateTypeAtomInMainExprTree te t) >>
                        when (not $ (checkIsAtom . fExpr) te) 
                               (updateTypeSelectType te t >>
                                updateMainExprTreeType t
                               ) >>
                        liftIO (labelNew $ Just $ show t) >>= 
                        \typeL -> 
                        liftIO (containerGetChildren tb) >>= \[oldL] ->
                        liftIO (containerRemove tb oldL) >> 
                        liftIO (containerRemove b eText) >> 
                        liftIO (set tb [containerChild := typeL]) >> 
                        liftIO (set b [containerChild := tb] >> widgetShowAll b)
                        >> return ()) >> 
                return ()

-- TODO : la usabamos para cambiar una sub-expresión en el arbol de tipado
-- ya no se si queremos esto.
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
                                                buildTreeExpr te >>
                                                return ()) >> 
                                return ()

-- | Aplica el type-checker a la expresión seleccionada.
typedCheckType :: IState ()
typedCheckType = getMainExprTree >>= \te ->
                 case checkPreExpr (toExpr $ fExpr te) of
                      Left err -> (reportErrWithErrPaned $ show err)
                      Right checkedType ->
                        case unify checkedType (fType te) emptySubst of
                          Left err' -> reportErrWithErrPaned $ show err'
                          Right _   -> getMainExprTree >>= \meTree ->
                                       highlightBox (eventExpr meTree) 
                                                    successfulBg >>
                                       highlightBox (eventType meTree) 
                                                    successfulBg
                                      -- reportSuccess "Los tipos coinciden."
                                      -- get >>= 
                                      -- liftIO . configEventCheckType (eventType te) checkedType

checkInExpr :: String -> IState (Maybe PreExpr)
checkInExpr s = case parseFromString s of
                        Left err -> (reportErrWithErrPaned $ show err) >> return Nothing
                        Right expr -> return $ Just expr

checkInType :: String -> IState (Maybe Type)
checkInType s = case parseTyFromString s of
                     Left err -> reportErrWithErrPaned (show err) >> return Nothing
                     Right t -> return $ Just t
-- 
-- | Navega una expresión (la seleccionada) y devuelve, si se puede
-- hacer la navegación, una caja de tipado correspondiente con el nodo
-- al que llegamos.
goTypedExpr :: (Focus -> Maybe Focus) -> ExprState -> IState (Maybe (ExprState, HBox, HBox))
goTypedExpr go te = case (go . fExpr) te of
                Nothing ->  return Nothing
                Just f ->   get >>= \s -> setupEventExpr f TyUnknown >>= 
                            \(eb,tb) -> liftIO (configEventSelectTypeFromTree tb s) >>
                            get >>= \s ->
                            return $ Just ((te' f eb tb), eb, tb)
    where (fwd,bwd) = (fromJust . go . f, fromJust . go . g)
          (f,g) = pathExpr te
          te' f eb tb = ExprState f TyUnknown (fwd,bwd) eb tb 

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
 
-- Setea el par expresión, tipo para construir el árbol de tipado.
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
                     Just se -> updateMainExprTree se >> buildTreeExpr se
                     Nothing -> reportErrWithErrPaned 
                                            "Ninguna expresion seleccionada."
