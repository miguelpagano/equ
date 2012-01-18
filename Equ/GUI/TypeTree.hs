-- | Aspectos de la interfaz independientes de las expresiones.
module Equ.GUI.TypeTree where

import Equ.PreExpr
import Equ.Syntax
import Equ.Parser
import Equ.TypeChecker
import Equ.Types
import Equ.Rule
import Equ.Theories
import Equ.Proof hiding (goDownL, goDownR, goTop, goUp)

import Equ.GUI.Utils
import Equ.GUI.Widget
import Equ.GUI.Types
import Equ.GUI.State
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

import Data.List (deleteBy, find)
import qualified Data.Serialize as S
import qualified Data.ByteString as L

-- Función principal que construye el arbol de tipado.
buildTreeExpr :: IState Focus -> (Focus -> IState ()) -> VBox -> 
                 HBox -> IState [ExprState]
buildTreeExpr isf fmp bTreeExpr we = do
                            f <- isf
                            fs <- return $ toFocusesWithGo $ fst f
                            [we'] <- io (containerGetChildren we)
                            mes <- io $ makeMainExprState f (castToHBox we')
                            io $ do 
                                bb <- hBoxNew False 0
                                boxPackStart bb (eventType mes) PackGrow 2
                                boxPackEnd bTreeExpr bb PackNatural 2
                                widgetShowAll bb
                            l <- buildTreeExpr' isf (castToHBox we') mes 
                                                    bTreeExpr [mes]
                            io $ boxPackStart bTreeExpr we PackGrow 5
                            configTypeEntry isf fmp bTreeExpr l l
                            return l
    where
        makeMainExprState :: Focus -> HBox -> IO ExprState
        makeMainExprState f we = 
                    do
                    t <- (case (checkPreExpr . fst) f of
                                 Left _ -> return TyUnknown
                                 Right t -> return t)
                    tb <- setupEventExpr f t we
                    return $ ExprState f t (id,id) we tb

-- Función secundaria que contruye el árbol de tipado.
buildTreeExpr' :: IState Focus -> HBox -> ExprState -> VBox -> 
                  [ExprState] -> IState [ExprState]
buildTreeExpr' isf we te bTree l = do
            leftBranch <- io $ goTypedExpr goDownL te
            rightBranch <- io $ goTypedExpr goDownR te
            case (leftBranch, rightBranch) of
                (Just (lf, lt, lp), Just (rf, rt, rp)) -> 
                    io (containerGetChildren we) >>= \[leb, _, reb] ->
                    makeExprState lf lt lp (castToHBox leb) >>= \dlte ->
                    makeExprState rf rt rp (castToHBox reb) >>= \drte ->
                    io (hBoxNew False 0) >>= \bTree' ->
                    io (boxPackEnd bTree bTree' PackNatural 2) >>
                    io (fillNewBox bTree' (eventType drte)) >>= \nVb ->
                    buildTreeExpr' isf (castToHBox reb) drte nVb 
                                        (dlte : drte : l) >>= \l' ->
                    io (fillNewBox bTree' (eventType dlte)) >>= \nVb ->
                    buildTreeExpr' isf (castToHBox leb) dlte nVb l'
                (Just (lf, lt, lp), Nothing) -> 
                    io (containerGetChildren we) >>= \[_, eb] ->
                    io (containerGetChildren (castToEventBox eb)) >>= \[leb] ->
                    makeExprState lf lt lp (castToHBox leb) >>= \dlte ->
                    io (hBoxNew False 0) >>= \bTree' ->
                    io (boxPackEnd bTree bTree' PackNatural 2) >>
                    io (fillNewBox bTree' (eventType dlte)) >>= \nVb ->
                    buildTreeExpr' isf (castToHBox leb) dlte nVb (dlte : l)
                (Nothing, _) -> return l
    where
        makeExprState :: Focus -> Type -> GoBack -> HBox -> IState ExprState
        makeExprState f t p eb = io (setupEventExpr f t eb) >>= \tb ->
                                 return $ ExprState f t p eb tb
        fillNewBox :: (BoxClass b) => b -> HBox -> IO VBox
        fillNewBox bTree tb = 
                            vBoxNew False 0 >>= \nVb ->
                            hBoxNew False 0 >>= \nb -> 
                            boxPackStart nb tb PackGrow 2 >> 
                            boxPackEnd nVb nb PackGrow 2 >> 
                            boxPackEnd bTree nVb PackGrow 2 >> 
                            widgetShowAll bTree >>
                            return nVb

paintBranchErr :: Focus -> [ExprState] -> IState ()
paintBranchErr f ess = paint (fromJust $ find (\e -> fExpr e == f) ess)
    where
        paint :: ExprState -> IState ()
        paint es = highlightBox (eventType es) errBg >>
                        (case goUp f of
                            Nothing -> return ()
                            (Just f') -> paintBranchErr f' ess)

-- | Aplica el type-checker a la expresión seleccionada.
typedCheckType :: Focus -> [ExprState] -> IState ()
typedCheckType f ess = case checkPreExpr (toExpr f) of
                    Left err -> paintBranchErr ((fst . fst) err) ess >>
                                (reportErrWithErrPaned $ show err)
                    Right checkedType -> return ()
--                         case unify checkedType (getTypeFocus f) emptySubst of
--                         Left err' -> reportErrWithErrPaned $ show err'
--                         Right _   -> undefined


configTypeEntry :: (IState Focus) -> (Focus -> IState ()) -> VBox -> 
                   [ExprState] -> [ExprState] -> IState ()
configTypeEntry _ _ _ [] _ = return ()
configTypeEntry isf fmp extBTree (es:ess) l = 
                            when ((checkIsAtom . fExpr) es) 
                            (configEventSelectTypeFromTree es)
                            >> configTypeEntry isf fmp extBTree ess l
    where
        configEventSelectTypeFromTree :: ExprState -> IState ()
        configEventSelectTypeFromTree es = 
                do
                b <- return $ (eventType es)
                [tb'] <- io $ containerGetChildren b
                tb <- return $ castToEventBox tb'
                s <- get
                io (tb `on` buttonPressEvent $ tryEvent (
                    eventWithState (
                        isf >>= \f ->
                        io (entryNew) >>= \eText ->
                        io (entrySetText eText (t f) >>
                                containerRemove b tb >>
                                boxPackStart b eText PackGrow 0 >> 
                                widgetShowAll b) >>
                        configTypeEntry' isf fmp eText b tb es
                                ) s ))
                return ()
            where   go :: Focus -> Focus
                    go = fst $ pathExpr es
                    t :: Focus -> String
                    t f = show $ getTypeFocus $ go f
    
        configTypeEntry' :: (IState Focus) -> (Focus -> IState ()) -> 
                            Entry -> HBox -> EventBox -> ExprState -> IState ()
        configTypeEntry' isf fmp eText b tb es = 
                        withState (onEntryActivate eText) 
                        (liftIO (entryGetText eText) >>= 
                        \text -> checkInType text >>= \checkText ->
                        case checkText of
                            Nothing -> return ()
                            Just t -> 
                                io (labelNew $ Just $ show t) >>= 
                                \typeL -> 
                                io (containerGetChildren tb) >>= \[oldL] ->
                                io (containerRemove tb oldL) >> 
                                io (containerRemove b eText) >> 
                                io (set tb [containerChild := typeL]) >> 
                                io (set b [containerChild := tb] >> 
                                    widgetShowAll b) >>
                                isf >>= \f ->
                                fmp (setAtomType (goTop f) (fst $ pathExpr es) t) >> 
                                io (containerGetChildren extBTree) >>= \wl ->
                                io (containerRemove extBTree (head wl)) >>
                                removeAllChildren extBTree >>
                                return (castToHBox $ head wl) >>= \we ->
                                buildTreeExpr isf fmp extBTree we >>= \l ->
                                isf >>= \f ->
                                typedCheckType f l >>
                                return ()) >> 
                        return ()

-- Configuración general para los botones. 
-- (Coloreo y desColoreo al pasar por encima)
configEventGeneralExpr :: (BoxClass w) => EventBox -> w -> IO ()
configEventGeneralExpr eb b = 
                            onEvent enterNotifyEvent (highlightBox b hoverBg) >>
                            onEvent leaveNotifyEvent (unlightBox b Nothing) >>
                            return ()
    where onEvent event action = eb `on` event $ tryEvent action

-- | Navega una expresión (la seleccionada) y devuelve, si se puede
-- hacer la navegación, una caja de tipado correspondiente con el nodo
-- al que llegamos.
goTypedExpr :: (Focus -> Maybe Focus) -> ExprState -> 
                    IO (Maybe (Focus, Type, GoBack))
goTypedExpr go te = 
                case (go . fExpr) te of
                    Nothing -> return Nothing
                    Just f ->  do
                               t <- (case (checkPreExpr . fst) f of
                                        Left _ -> return TyUnknown
                                        Right t -> return t)
                               return $ Just (f, t, (fwd, bwd))
    where 
        (f,g) = pathExpr te
        (fwd,bwd) = (fromJust . go . f, fromJust . go . g)

configEventGeneralExprBeta :: (BoxClass w) => EventBox -> w -> IO ()
configEventGeneralExprBeta eb b = 
                            onEvent enterNotifyEvent (highlightBox b hoverBg) >>
                            onEvent leaveNotifyEvent (unlightBox b Nothing) >>
                            return ()
    where onEvent event action = eb `on` event $ tryEvent action


-- Setea el par expresión, tipo para construir el árbol de tipado.
setupEventExpr :: Focus -> Type -> HBox -> IO HBox
setupEventExpr (e,_) t exprEbb = do
                                typeL <- labelNew $ Just $ show t
                                typeEb <- eventBoxNew
                                typeEbb <- hBoxNew False 0
                                configEventGeneralExprBeta typeEb exprEbb
                                configEventGeneralExpr typeEb typeEbb
                                set typeEb [ containerChild := typeL ]
                                set typeEbb [ containerChild := typeEb ]
                                return typeEbb

-- | Checkeo del tipo ingresado para la expresión.
checkInType :: String -> IState (Maybe Type)
checkInType s = case parseTyFromString s of
                     Left err -> reportErrWithErrPaned (show err) >> 
                                 return Nothing
                     Right t -> return $ Just t
