-- | Aspectos de la interfaz independientes de las expresiones.
module Equ.GUI.Widget where

import Equ.GUI.Types
import Equ.GUI.Utils
import Equ.GUI.Settings
import Equ.Rule
import Equ.Theories
import Equ.Proof
import Equ.PreExpr

import Graphics.UI.Gtk hiding (eventButton, eventSent,get)
import qualified Graphics.UI.Gtk as G
import Graphics.UI.Gtk.Gdk.EventM
import Graphics.UI.Gtk.Glade (GladeXML,xmlGetWidget)
import Data.Reference
import Data.Maybe(fromJust)
import Control.Monad.Trans(lift,liftIO)
import Control.Monad.State(get,evalStateT)
import Data.Text(unpack)

    
-- | Abstracción de la acción que queremos realizar al cerrar la ventana.
quitAction :: Window -> IO ()
quitAction w = widgetDestroy w

-- | Obtener un elemento del menú.
getMenuButton :: GladeXML -> String -> IO MenuItem
getMenuButton w = xmlGetWidget w castToMenuItem 


{- Las siguientes acciones muestran y ocultan la lista de símbolos. -}
openSymFrame :: IState ()
openSymFrame = do
    f <- getSymFrame
    liftIO (widgetShowAll f)
   
--    \p ->
--               liftIO (set p [ panedPositionSet := True 
--                             , panedPosition := paneSymbolWidth ] >>
--                       widgetShowAll p)
   
hideSymFrame :: IState ()
hideSymFrame = do
    f <- getSymFrame
    name <- liftIO $ G.get f widgetName
    liftIO $ putStrLn "\nPROBANDO HIDESYMPANE:"
    liftIO $ putStrLn (maybe "No name" (\n -> if null n then "Nombre vacio" else n) name)
    liftIO $ putStrLn "END PROBANDO HIDESYMPANE\n"
    main_box <- getParentNamed "mainBox" $ toWidget f
    liftIO (widgetHideAll f)
    
openAxiomFrame :: IState ()
openAxiomFrame = do
    f <- getAxiomFrame
    liftIO (widgetShow f)
    
hideAxiomFrame :: IState ()
hideAxiomFrame = do
    f <- getAxiomFrame
    liftIO (widgetHideAll f)

--     getSymPane >>= \p -> 
--               liftIO (set p [ panedPositionSet := True 
--                             , panedPosition := 0 ] >>
--                       widgetShowAll p)
   
   
-- hideSymPane :: IState ()
-- hideSymPane = getSymPane >>= \p -> 
--               liftIO (set p [ panedPositionSet := True 
--                             , panedPosition := 0 ] >>
--                       widgetShowAll p)
   
   
openErrPane :: IState ()
openErrPane = getFormErrPane >>= \erp ->
              liftIO (set erp [ panedPositionSet := True 
                              , panedPosition := paneErrPaneHeight ] >>
                      widgetShowAll erp)

-- | Crea un label, en el cual al texto le coloca un string.
setupLabelPreExpr :: String -> IO Label
setupLabelPreExpr s = (labelNew $ Just s) >>= \lab ->
                        set lab [ miscXalign := 0
                                , widgetHeightRequest := 30
                                , labelSelectable := True
                                ] >>
                        widgetShowAll lab >>
                        return lab

-- | Hace un update de la lista de expresiones ingresadas.
updateTypedList :: VBox -> IState ()
updateTypedList b = getExpr >>= 
                    \(e, _) -> liftIO (
                                setupLabelPreExpr ("$\t" ++ show e) >>= 
                                \lab -> (boxPackStart b lab PackNatural 2) >> 
                                widgetShowAll b)

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

{- Las siguientes acciones crean widgets como computaciones en la
mónada IState. -} 

-- | Una caja con cierto padding.
newBox :: IState HBox
newBox = liftIO (hBoxNew False 0)

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
addToBox :: (BoxClass b,WidgetClass w) => b -> w -> IRProof
addToBox b w = liftIO $ boxPackStart b w PackGrow 0

-- | Elimina todos los controles contenidos en una caja (también
-- destruye los hijos para liberar memoria -- está bien hacer esto?).
removeAllChildren :: HBox -> IRProof
removeAllChildren b = liftIO $ containerForeach b $ 
                         \x -> containerRemove b x >> widgetDestroy x

-- | Poné en una caja el widget que usamos para construir nuevas
-- expresiones.
setupForm ::  HBox -> IRProof
setupForm b = labelStr "?" >>= setupFormEv b

-- (MANU) Por qué la funcion que sigue es tan general si solo la usamos en setupForm?

-- | Asigna los manejadores de eventos para widgets de expresiones a 
-- los controles.
setupFormEv :: WidgetClass w => HBox -> w -> IRProof
setupFormEv b c = liftIO eventBoxNew >>= \eb ->
                  addToBox b eb >>
                  liftIO (set eb [ containerChild := c ]) >>
                  setupEvents b eb

-- | Define los manejadores de eventos para una caja que tiene el
-- widget para construir expresiones.
setupEvents :: WidgetClass w => HBox -> w -> IRProof
setupEvents b eb = do s <- get
                      ProofState _ sym e@(ExprFocus _ p i) _ _ axiom <- readRef s
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
removeExpr :: HBox -> ProofRef -> EventM EButton ()
removeExpr b s = do RightButton <- eventButton
                    eventWithState (updateExpr holeExpr >>
                                    removeAllChildren b >>
                                    setupForm b) s
                    liftIO $ widgetShowAll b
                    return ()

-- | Si se aprieta el botón izquierdo, empezamos a trabajar en este
-- control y luego pasamos el control a la lista de símbolos.
newFocusToSym :: WidgetClass w => HBox -> GoBack -> w -> ProofRef -> EventM EButton ()
newFocusToSym l f sym s = do LeftButton <- eventButton 
                             eventWithState (updateFrmCtrl l >>
                                             updatePath f >> 
                                             openSymFrame ) s
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
