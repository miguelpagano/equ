-- | Aspectos de la interfaz independientes de las expresiones.
module Equ.GUI.Widget where

import Equ.PreExpr
import Equ.Parser
import Equ.TypeChecker
import Equ.Types

import Equ.GUI.Types
import Equ.GUI.Utils
import Equ.GUI.Settings

import Graphics.UI.Gtk hiding (eventButton, eventSent,get)
import Graphics.UI.Gtk.Gdk.EventM
import Graphics.UI.Gtk.Glade (GladeXML,xmlGetWidget)
import Data.Reference
import Data.Maybe(fromJust)
import Control.Monad.Trans(lift,liftIO)
import Control.Monad.State(get)
import Control.Monad(filterM) 

-- | Abstracción de la acción que queremos realizar al cerrar la ventana.
quitAction :: Window -> IO ()
quitAction w = widgetDestroy w

-- | Obtener un elemento del menú.
getMenuButton :: GladeXML -> String -> IO MenuItem
getMenuButton w = xmlGetWidget w castToMenuItem 


{- Las siguientes acciones muestran y ocultan la lista de símbolos. -}
openSymPane :: IState ()
openSymPane = getSymPane >>= \p ->
              liftIO (set p [ panedPositionSet := True 
                            , panedPosition := paneSymbolWidth ] >>
                      widgetShowAll p)

-- | Reportar errores usando la panel de errores. Toma un mensaje de error y 
-- lo muestra en el panel. TODO: Que pasa si el string es muuuuuy largo. 
-- ¿Sería buena idea pasarle el formato con el string para mas versatilidad?
reportErrWithErrPaned :: String -> IState ()
reportErrWithErrPaned s = getErrPanedLabel >>=
                          \l -> liftIO (labelSetMarkup l 
                                            (markSpan 
                                            [ FontBackground "#FF0000"
                                            , FontForeground "#000000"
                                            ] 
                                            s)) >>
                          openErrPane

-- | Abre el panel de error.
openErrPane :: IState ()
openErrPane = getFormErrPane >>= \erp ->
              liftIO (set erp [ panedPositionSet := True 
                              , panedPosition := paneErrPaneHeight ] >>
                      widgetShowAll erp)

-- | Setea un boton activable con la expresion ingresada.
setupTbPreExpr :: String -> IState ToggleButton
setupTbPreExpr s = liftIO ( toggleButtonNewWithLabel s >>= \exprTb ->
                            set exprTb [ buttonRelief := ReliefNone
                                       , widgetHeightRequest := 40
                                       ] >>
                            widgetShowAll exprTb >>
                            return exprTb)

-- | Desactiva el boton activable siempre que no sea el pasado en el primer
-- argumento. TODO: Que pasa si el widget no es un toggleButton (?)
resetActiveTb :: WidgetClass w => Maybe ToggleButton -> w -> IO ()
resetActiveTb Nothing w = set (castToToggleButton w) [toggleButtonActive := False]
resetActiveTb (Just tb) w = let w' = (castToToggleButton w)
                            in case tb == w' of
                                    True -> return ()
                                    False -> set w' [toggleButtonActive := False]

-- | Desactiva un boton activable.
resetAllActiveTb :: WidgetClass w => w -> IO ()
resetAllActiveTb = resetActiveTb Nothing

-- | Cuando se activa un boton activable dentro de un contenedor, se desactiva 
-- el resto, es decir, una exclusion de activacion mutua dentro del contenedor.
selectToggleButton :: (ContainerClass c) => c -> ToggleButton -> IState ()
selectToggleButton b tb = liftIO (toggleButtonGetActive tb) >>= 
                          \tbActive -> 
                            if tbActive then 
                                openTypedOptionPane >> 
                                liftIO (containerForeach b $ 
                                             resetActiveTb $ Just tb)
                            else return ()

-- | Hace un update de la lista de expresiones ingresadas.
updateTypedList :: IState ()
updateTypedList = getTypedFormBox >>=
                    \b -> getExpr >>= 
                    \(e, _) ->  setupTbPreExpr (show e) >>=
                    \tb -> liftIO (boxPackStart b tb PackNatural 2) >>
                    addToggleButtonList e tb >>
                    withState (onToggled tb) (selectToggleButton b tb) >>
                    return ()

-- | Configura los botones activables que representan las expresiones, en el
-- arbol de tipado.
configToggleButton :: ToggleButton -> IState ()
configToggleButton tb = getBoxTypedFormTree >>=
                        \b -> withState (onToggled tb) 
                                        (return ()) >>
                        --(selectToggleButton b tb) >>
                        return ()

-- Función principal que construye el arbol de tipado.
-- TODO: Esta muy feo hacerlo en base al string, de todas formas parte de
-- la nueva estructura que hice esta pensado para solucionar esto.
buildTypedFormTree :: String -> IState ()
buildTypedFormTree s = case parseFromString s of   
                            Right expr ->
                                    getBoxTypedFormTree >>= \bTree -> 
                                    (buildTypedFormTree' . toFocus) expr $ bTree
                            Left err -> reportErrWithErrPaned $ show err

-- Creería que una vez que este andando la nueva estructura esta va a pasar 
-- a ser la principal.
buildTypedFormTree' :: (BoxClass b) => Focus -> b -> IState ()
buildTypedFormTree' f@(e,_) bTree = 
            case checkPreExpr e of
                Left err -> reportErrWithErrPaned $ show err
                Right te -> 
                    setupTbPreExpr (show e ++ " : " ++ show te) >>=
                    \tb -> configToggleButton tb >>
                    liftIO (boxPackEnd bTree tb PackNatural 2) >>
                    case (goDown f, goDownR f) of
                        (Just df, Just dRf) -> 
                                newBox >>= \nb -> 
                                fillNewBox bTree nb >>=
                                \nVb -> buildTypedFormTree' dRf nVb >>
                                fillNewBox bTree nb >>=
                                \nVb -> buildTypedFormTree' df nVb
                        (Just df, Nothing) -> 
                                newBox >>= \nb -> 
                                fillNewBox bTree nb >>=
                                \nVb -> buildTypedFormTree' df nVb
                        (Nothing, _) -> return ()
    where
        fillNewBox :: (BoxClass b, BoxClass b') => b -> b' -> IState VBox
        fillNewBox bTree nb = newVBox >>=
                              \nVb ->liftIO (boxPackEnd nb nVb PackGrow 2) >>
                              liftIO (boxPackEnd bTree nb PackGrow 2) >>
                              return nVb

-- | En base a una expresion seleccionada genera el arbol de tipado y abre
-- el respectivo panel.
typedExprTree :: IState ()
typedExprTree = getTypedFormBox >>=
                \b -> liftIO (activeTb b) >>=
                \r -> case r of
                        Nothing -> reportErrWithErrPaned 
                                            "Ninguna expresion seleccionada."
                        Just tb -> liftIO (buttonGetLabel tb) >>= 
                                   \e -> buildTypedFormTree e >>
                                   openTypedFormPane

-- | Retorna el boton activado, si no Nothing, en el contenedor VBox.
-- TODO: Creo que tuve algun problemas de tipos cuando quise generalizar
-- la signatura de esta función.
activeTb :: VBox -> IO (Maybe ToggleButton)
activeTb b = containerGetChildren b >>= 
            \c -> filterM (toggleButtonGetActive . castToToggleButton) c >>=
            \c' -> case c' of
                        [] -> return Nothing
                        w:_ -> return . Just $ castToToggleButton w

-- | Borra una expresión seleccionada de una lista.
typedExprRemove :: IState ()
typedExprRemove = getTypedFormBox >>=
                  \b -> liftIO (activeTb b) >>=
                  \r -> case r of
                        Nothing -> reportErrWithErrPaned 
                                            "Ninguna expresion seleccionada."
                        Just tb -> liftIO (containerRemove b tb)

-- Elimina todos los widget's de una contenedor.
cleanContainer :: (ContainerClass c) => c -> IState ()
cleanContainer c = liftIO (containerForeach c $ containerRemove c)

-- | Remueve todas las expresiones ingresadas, es decir, las contenidas en la
-- lista.
typedExprRemoveAll :: IState ()
typedExprRemoveAll = getTypedFormBox >>= \b -> cleanContainer b

-- | Limpia el arbol de tipado de una expresión.
cleanTypedFormPane :: IState ()
cleanTypedFormPane = getBoxTypedFormTree >>= \bTree -> cleanContainer bTree

hideSymPane :: IState ()
hideSymPane = getSymPane >>= \p -> 
              liftIO (set p [ panedPositionSet := True 
                            , panedPosition := 0 ] >>
                      widgetShowAll p)

{- Las siguientes acciones muestran y ocultan el widget de fórmulas . -}
openFormPane :: HBox -> Paned -> IState ()
openFormPane b p = liftIO (widgetShow b >>
                           set p [ panedPositionSet := True 
                                 , panedPosition := paneFormHeight 
                                 ] >>
                           widgetShowAll p)

hideFormPane :: HBox -> Paned -> IState ()
hideFormPane b p = liftIO (widgetHide b >>
                           set p [ panedPosition := 0 
                                 , panedPositionSet := True ] >>
                           widgetShowAll p
                           )

-- | Abre el meno de opciones para las expresiones ingresadas.
-- TODO: Faltaría prestar atención a los valores necesarios para hacer
-- las definiciones correctas de las posiciones.
openTypedOptionPane :: IState ()
openTypedOptionPane = getTypedOptionPane >>= 
                      \p ->liftIO (set p [ panedPositionSet := True 
                                         , panedPosition := 1300
                                         ] >>
                                   widgetShowAll p
                                  )

-- | Igual que arriba pero para cerrar el panel.
hideTypedOptionPane :: IState ()
hideTypedOptionPane = getTypedOptionPane >>= 
                      \p -> liftIO (set p [ panedPosition := 2000
                                          , panedPositionSet := True ] >>
                                    widgetShowAll p
                                   )

-- | Abre el panel para mostrar el arbol de tipado de una expresión.
openTypedFormPane :: IState ()
openTypedFormPane = getTypedFormPane >>= 
                      \p ->liftIO (set p [ panedPositionSet := True 
                                         , panedPosition := 0
                                         ] >>
                                   widgetShowAll p
                                  )

hideTypedFormPane :: IState ()
hideTypedFormPane = getTypedFormPane >>= 
                      \p -> liftIO (set p [ panedPosition := 3000
                                          , panedPositionSet := True ] >>
                                    widgetShowAll p
                                   )

{- Las siguientes acciones crean widgets como computaciones en la
mónada IState. -} 

-- | Una caja con cierto padding.
newBox :: IState HBox
newBox = liftIO (hBoxNew False 0)

newVBox :: IState VBox
newVBox = liftIO (vBoxNew False 0)

-- | Una nueva caja de texto.
newEntry :: IState Entry
newEntry = liftIO entryNew

-- | Una nueva etiqueta.
labelStr :: String -> IState Label
labelStr = liftIO . labelNew . return


-- | Redimensiona una caja de texto.
entryDim :: Entry -> Int -> IState ()
entryDim entry l = liftIO $ widgetSetSizeRequest entry l (-1)


-- | Pone un widget dentro de una caja.
addToBox :: (BoxClass b,WidgetClass w) => b -> w -> IRExpr
addToBox b w = liftIO $ boxPackStart b w PackGrow 0

-- | Elimina todos los controles contenidos en una caja (también
-- destruye los hijos para liberar memoria -- está bien hacer esto?).
removeAllChildren :: HBox -> IRExpr
removeAllChildren b = liftIO $ containerForeach b $ 
                         \x -> containerRemove b x >> widgetDestroy x

-- | Poné en una caja el widget que usamos para construir nuevas
-- expresiones.
setupForm ::  HBox -> IRExpr
setupForm b = labelStr "?" >>= setupFormEv b

-- | Asigna los manejadores de eventos para widgets de expresiones a 
-- los controles.
setupFormEv :: WidgetClass w => HBox -> w -> IRExpr
setupFormEv b c = liftIO eventBoxNew >>= \eb ->
                  addToBox b eb >>
                  liftIO (set eb [ containerChild := c ]) >>
                  setupEvents b eb

-- | Define los manejadores de eventos para una caja que tiene el
-- widget para construir expresiones.
setupEvents :: WidgetClass w => HBox -> w -> IRExpr
setupEvents b eb = do s <- get
                      GState _ i _ _ sym p _ <- readRef s
                      st <- liftIO $ widgetGetStyle b
                      bg <- liftIO $ styleGetBackground st (toEnum 0)
                      liftIO $ eb `on` enterNotifyEvent $ tryEvent $ highlightBox b hoverBg
                      liftIO $ eb `on` leaveNotifyEvent $ tryEvent $ unlightBox b bg
                      liftIO $ eb `on` buttonPressEvent $ tryEvent $ newFocusToSym b p sym s
                      liftIO $ eb `on` buttonPressEvent $ tryEvent $ removeExpr b s
                      return ()


{- Las siguientes funciones son los manejadores de eventos. -}

-- | Si apretamos el botón derecho, entonces borramos la expresión
-- enfocada.
removeExpr :: HBox -> GRef -> EventM EButton ()
removeExpr b s = do RightButton <- eventButton
                    eventWithState (updateExpr holeExpr >>
                                    removeAllChildren b >>
                                    setupForm b) s
                    liftIO $ widgetShowAll b
                    return ()

-- | Si se aprieta el botón izquierdo, empezamos a trabajar en este
-- control y luego pasamos el control a la lista de símbolos.
newFocusToSym :: WidgetClass w => HBox -> GoBack -> w -> GRef -> EventM EButton ()
newFocusToSym l f sym s = do LeftButton <- eventButton 
                             eventWithState (updateFrmCtrl l >>
                                             updatePath f >> 
                                             openSymPane ) s
                             liftIO $ highlightBox l focusBg
                             liftIO $ widgetGrabFocus sym
                             return ()

-- | Resalta todos los controles que están dentro de una caja.
highlightBox b bg = liftIO $ containerForeach b (highlight bg)

-- | Quita el resaltado a los controles que están dentro de una caja.
unlightBox b bg = liftIO $ containerForeach b (unlight bg) 


-- | Cambia el color de fondo de un control.
highlight :: WidgetClass w => Color -> w -> IO ()
highlight bg w = widgetModifyBg w (toEnum 0) bg


-- | Le quita el color especial a un control.
unlight :: WidgetClass w => Color -> w -> IO ()
unlight bg w = widgetModifyBg w (toEnum 0) bg
