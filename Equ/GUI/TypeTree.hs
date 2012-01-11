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

import Data.List (deleteBy)
import qualified Data.Serialize as S
import qualified Data.ByteString as L

-- Función principal que construye el arbol de tipado.
buildTreeExpr :: ExprState -> IState ()
buildTreeExpr te = 
                get >>= \ s ->
                getTreeExprBox >>= \ bTreeExpr -> 
                getTreeOpBox >>= \bTreeOp ->
                getTreeVarQBox >>= \bTreeVarQ ->
                getTreeQuantBox >>= \bTreeQuant ->
                removeAllChildren bTreeExpr >>
                removeAllChildren bTreeOp >>
                removeAllChildren bTreeVarQ >>
                removeAllChildren bTreeQuant >>
                setupEventExpr (fExpr te) TyUnknown >>= 
                \(eb, tb) -> newBox >>= \ bb -> 
                addMainExprToTree (fExpr te) t (id,id) eb tb >>= \te ->
                when ((isPreExprQuant . fExpr) te)
                    (addQuantExprTree te) >>
                liftIO (configEventSelectTypeFromTree tb s >>
                        boxPackStart bb eb PackGrow 2 >>
                        boxPackStart bb tb PackGrow 2 >>
                        boxPackEnd bTreeExpr bb PackNatural 2 >>
                        widgetShowAll bb
                        ) >>
                buildTreeExpr' te bTreeExpr >>
                updateOpExprTree (agrupOp $ toFocusesWithGo $ fst $ fExpr te)
                                    Nothing Nothing >>
                buildTreeOpList bTreeOp >>
                buildTreeVarQList bTreeVarQ >>
                buildTreeQuantList bTreeQuant
    where
        tVar :: Type
        tVar = getVarTypeFromQuantType (getTypeFocus $ fExpr te)
        t :: Type
        t = case (isPreExprQuant . fExpr) te of
                True -> tVar :-> TyUnknown
                False -> TyUnknown

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
                                (addAtomExprTree dlte) >>
                            when ((isPreExprQuant . fExpr) dlte) 
                                (addQuantExprTree dlte) >>
                            buildTreeExpr' drte nVb >>
                            fillNewBox bTree' leb ltb dlte >>= \nVb ->
                            when ((checkIsAtom . fExpr) drte) 
                                (addAtomExprTree drte) >>
                            when ((isPreExprQuant . fExpr) drte) 
                                (addQuantExprTree drte) >>
                            buildTreeExpr' dlte nVb
                        (Just (dlte, leb, ltb), Nothing) -> 
                            newBox >>= \bTree' ->
                            liftIO (boxPackEnd bTree bTree' PackNatural 2) >>
                            fillNewBox bTree' leb ltb dlte >>= \nVb ->
                            when ((checkIsAtom . fExpr) dlte) 
                                (addAtomExprTree dlte) >>
                            when ((isPreExprQuant . fExpr) dlte) 
                                (addQuantExprTree dlte) >>
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

-- Versión general para la construcción del árbol de tipado de cuantificadores.
buildTreeXList ::   VBox ->
                    (Focus -> String) ->
                    (Type -> Type) ->
                    (HBox -> HBox -> GRef -> IO (ConnectId EventBox)) ->
                    IState ()
buildTreeXList b fToS getTypeT funConfig = 
    getQuantExprTree >>= \qet ->
    get >>= \s ->
    liftIO (build qet b s)
    where
        t :: Type -> Type
        t ty = getTypeT ty
        build :: [ExprState] -> VBox -> GRef -> IO ()
        build [] b s = widgetShowAll b
        build (e:es) b s = 
                        do
                        typeL <- labelNew $ Just $ show $ t (fType e)
                        typeEb <- eventBoxNew
                        typeEbb <- hBoxNew False 0
                        set typeL [miscXalign := 0.005]
                        configEventGeneralExprQuant typeEb typeEbb (eventExpr e)
                        set typeEb [ containerChild := typeL ]
                        boxPackStart typeEbb typeEb PackGrow 0
                        funConfig typeEbb (eventType e) s
                        exprL <- labelNew $ Just $ (fToS $ fExpr e) ++ " : "
                        set exprL [miscXalign := 0.005]
                        exprEb <- eventBoxNew
                        exprEbb <- hBoxNew False 0
                        set exprEb [ containerChild := exprL ]
                        boxPackStart exprEbb exprEb PackNatural 0
                        b' <- hBoxNew False 0
                        boxPackStart b' exprEbb PackNatural 0
                        set b' [ containerChild := typeEbb ]
                        set b [ containerChild := b' ]
                        build es b s

-- Versión general de configuración del campo de ingreso de tipos para 
-- cuantificadores.
configEventInTypeX :: HBox -> HBox -> GRef -> 
                      (Type -> Type) ->
                      (ExprState -> Entry -> HBox -> EventBox -> IState ()) ->
                      IO (ConnectId EventBox)
configEventInTypeX b b' s getXType configTypeXE= 
                        containerGetChildren b >>= \[tb'] ->
                        do
                        tb <- return $ castToEventBox tb'
                        tb `on` buttonPressEvent $ tryEvent $ 
                            eventWithState (
                                selectTypeFromBox b' >>
                                getSelectExpr >>= \(Just te) ->
                                liftIO (entryNew) >>= \eText ->
                                liftIO (entrySetText eText (show $ t (fType te)) >>
                                        containerRemove b tb >>
                                        boxPackStart b eText PackGrow 0 >> 
                                        widgetShowAll b) >>
                                        configTypeXE te eText b tb) s
    where
        t :: Type -> Type
        t ty = getXType ty

-- Versión general para el ingreso de tipos para cuantificadores.
configTypeXEntry :: ExprState -> Entry -> HBox -> EventBox -> 
                    (ExprState -> Type -> IState ()) ->
                    (Type -> Type) ->
                    (Type -> Type -> Type) ->
                    IState ()
configTypeXEntry es eText b tb updateTypeXInMainExprTree getXType ft = 
            liftIO (eText `on` keyPressEvent $ tryEvent (entryImContextFilterKeypress eText >>= \test -> 
                                                        liftIO (debug (show test)) >> return ())) >>
            withState (onEntryActivate eText) 
                (liftIO (entryGetText eText) >>= 
                \text -> checkInType text >>= \checkText ->
                case checkText of
                    Nothing -> return ()
                    Just t -> 
                        updateTypeXInMainExprTree es t >>
                        updateTypeQuantInExprTree es (ft t $ t' (fType es)) >>
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
    where
        t' :: Type -> Type
        t' ty = getXType ty

buildTreeQuantList :: VBox -> IState ()
buildTreeQuantList b = buildTreeXList 
                                b 
                                (show . fst . fromJust . getQAndVarFromQuant)
                                getQTypeFromQuantType
                                configEventInTypeQuant

buildTreeVarQList :: VBox -> IState ()
buildTreeVarQList b = buildTreeXList 
                                b
                                (show . snd . fromJust . getQAndVarFromQuant)
                                getVarTypeFromQuantType 
                                configEventInTypeVarQ

configTypeVarQEntry :: ExprState -> Entry -> HBox -> EventBox -> IState ()
configTypeVarQEntry es eText b tb = configTypeXEntry es eText b tb
                                        updateTypeVarQInMainExprTree
                                        getQTypeFromQuantType
                                        (\t -> \t' -> t :-> t')

configTypeQuantEntry :: ExprState -> Entry -> HBox -> EventBox -> IState ()
configTypeQuantEntry es eText b tb = configTypeXEntry es eText b tb 
                                        updateTypeQuantInMainExprTree                                        
                                        getVarTypeFromQuantType
                                        (\t -> \t' -> t' :-> t)

configEventInTypeQuant :: HBox -> HBox -> GRef -> IO (ConnectId EventBox)
configEventInTypeQuant b b' s = configEventInTypeX b b' s 
                                                   getQTypeFromQuantType
                                                   configTypeQuantEntry

configEventInTypeVarQ :: HBox -> HBox -> GRef -> IO (ConnectId EventBox)
configEventInTypeVarQ b b' s = configEventInTypeX b b' s 
                                                  getVarTypeFromQuantType
                                                  configTypeVarQEntry

-- Construye la lista de operadores.
buildTreeOpList :: VBox -> IState ()
buildTreeOpList b = get >>= \s -> getOpExprTree >>= \fs -> (liftIO $ build fs b s)
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
                            onEvent leaveNotifyEvent (unlightBox b Nothing) >>
                            return ()
    where onEvent event action = eb `on` event $ tryEvent action

-- Configuración para los botones de expresiones cuantificador.
configEventGeneralExprQuant :: (BoxClass w) => EventBox -> w ->  w -> IO ()
configEventGeneralExprQuant eb b b' = 
                            onEvent enterNotifyEvent (highlightBox b' hoverBg >>
                                                     highlightBox b hoverBg) >>
                            onEvent leaveNotifyEvent (unlightBox b' Nothing >>
                                                     unlightBox b Nothing) >>
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
                             (updateTypeAtomInMainExprTree te t >>
                              updateTypeAtomInExprTree te t
                              ) >>
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

-- Propagación de coloreo de error de las sub-expresiones.
paintBranchErr :: Focus -> IState ()
paintBranchErr f =  searchFocusInTree f >>= \fs ->
                    liftIO (debug $ show $ map (fExpr) fs) >>
                    paint fs
    where
        paint :: [ExprState] -> IState ()
        paint [] = return ()
        paint (es:ess) = highlightBox (eventExpr es) errBg >>
                        (case goUp f of
                            Nothing -> return ()
                            (Just f') -> paintBranchErr f') >>
                        paint ess

-- | Aplica el type-checker a la expresión seleccionada.
typedCheckType :: IState ()
typedCheckType = getMainExprTree >>= \te ->
                 case checkPreExpr (toExpr $ fExpr te) of
                    Left err -> paintBranchErr ((fst . fst) err) >>
                                (reportErrWithErrPaned $ show err)
                    Right checkedType ->
                        case unify checkedType (fType te) emptySubst of
                        Left err' -> reportErrWithErrPaned $ show err'
                        Right _   -> highlightBox (eventExpr te) 
                                                    successfulBg >>
                                    highlightBox (eventType te) 
                                                    successfulBg

-- | Checkeo del tipo ingresado para la expresión.
checkInType :: String -> IState (Maybe Type)
checkInType s = case parseTyFromString s of
                     Left err -> reportErrWithErrPaned (show err) >> 
                                 return Nothing
                     Right t -> return $ Just t
-- 
-- | Navega una expresión (la seleccionada) y devuelve, si se puede
-- hacer la navegación, una caja de tipado correspondiente con el nodo
-- al que llegamos.
goTypedExpr :: (Focus -> Maybe Focus) -> ExprState -> 
               IState (Maybe (ExprState, HBox, HBox))
goTypedExpr go te = case (go . fExpr) te of
                Nothing ->  return Nothing
                Just f ->   get >>= \s -> setupEventExpr f (getTypeFocus f) >>= 
                            \(eb,tb) -> 
                            liftIO (debug $ (show f) ++ show (getTypeFocus f)) >>
                            liftIO (configEventSelectTypeFromTree tb s) >>
                            return (Just ((te' f eb tb), eb, tb))
    where 
        (f,g) = pathExpr te
        (fwd,bwd) = (fromJust . go . f, fromJust . go . g)
        te' f eb tb = ExprState f (getTypeFocus f) (fwd,bwd) eb tb 
 
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
                     Just se -> 
                        updateMainExprTree se >> 
                        buildTreeExpr se
                     Nothing -> reportErrWithErrPaned 
                                            "Ninguna expresion seleccionada."

-- | Limpia todos los tipos asociados a una preExpresion.
cleanTypeInTree :: IState ()
cleanTypeInTree = getMainExprTree >>= \met ->
                  updateMainExprTree (se' met) >> 
                  buildTreeExpr (se' met)
    where se' :: ExprState -> ExprState
          se' se = se {fExpr = goTop $ resetTypeAllFocus (fExpr se)}
