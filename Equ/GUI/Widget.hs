-- | Aspectos de la interfaz independientes de las expresiones.
module Equ.GUI.Widget where

import Equ.PreExpr
import Equ.Parser
import Equ.TypeChecker
import Equ.Types
import Equ.Rule
import Equ.Theories
-- import Equ.GUI.SymbolList
import Equ.Proof hiding (goDownL, goDownR)


import Equ.GUI.Types
import Equ.GUI.State
import Equ.GUI.State.Expr
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

import Data.Text(unpack)

import Data.List (deleteBy)
import qualified Data.Serialize as S
import qualified Data.ByteString as L

import Graphics.Rendering.Pango.Font




-- unselectAll :: IconView -> IState ()
-- unselectAll tv = liftIO (treeViewGetSelection tv >>= \tree -> 
--                          treeSelectionSetMode tree SelectionSingle >>
--                          treeSelectionUnselectAll tree)
--     
-- | Abstracción de la acción que queremos realizar al cerrar la ventana.
quitAction :: Window -> IO ()
quitAction w = widgetDestroy w

-- | Obtener un elemento del menú.
getMenuButton :: GladeXML -> String -> IO MenuItem
getMenuButton w = xmlGetWidget w castToMenuItem 


{- Las siguientes acciones muestran y ocultan la lista de símbolos. -}
openSymFrame :: IState ()
openSymFrame = getSymFrame >>= liftIO . widgetShowAll

hideSymFrame :: IState ()
hideSymFrame = do
    f <- getSymFrame
    name <- liftIO $ G.get f widgetName
    liftIO $ debug "\nPROBANDO HIDESYMPANE:"
    liftIO $ debug (maybe "No name" (\n -> if null n then "Nombre vacio" else n) name)
    liftIO $ debug "END PROBANDO HIDESYMPANE\n"
    main_box <- getParentNamed "mainBox" $ toWidget f
    liftIO (widgetHideAll f)
    
openAxiomFrame :: IState ()
openAxiomFrame = getAxiomFrame >>= liftIO . widgetShow
   
hideAxiomFrame :: IState ()
hideAxiomFrame = getAxiomFrame >>= liftIO . widgetHideAll

-- | Reportar errores usando la panel de errores. Toma un mensaje de error y 
-- lo muestra en el panel. TODO: Que pasa si el string es muuuuuy largo. 
reportErrWithErrPaned :: String -> IState ()
reportErrWithErrPaned s = setErrMessage s >> openErrPane


-- | Reportar resultados exitosos en la consola.
reportSuccess :: String -> IState ()
reportSuccess = liftIO . debug


-- | Abre el panel de error.
openErrPane :: IState ()
openErrPane = getErrPane >>= \erp ->
              liftIO (set erp [ panedPositionSet := True 
                              , panedPosition := paneErrPaneHeight ] >>
                      widgetShowAll erp)
                      
setErrMessage :: String -> IState ()
setErrMessage msg = getErrPanedLabel >>= \eb ->
                    liftIO (containerGetChildren eb) >>=
                    \[l] -> liftIO (labelSetMarkup (castToLabel l) 
                                    (markSpan 
                                    [ FontBackground "#FF0000"
                                    , FontForeground "#000000"
                                    ] 
                                    msg)) >>
                    get >>= \s' ->
                    liftIO (eb `on` buttonPressEvent $ tryEvent $ 
                                    eventWithState (closeErrPane) s') >> 
                    return ()

closeErrPane :: IState ()
closeErrPane = getErrPane >>= \erp ->
               liftIO (set erp [ panedPositionSet := True 
                               , panedPosition := 0 ] >>
                       widgetShowAll erp)


-- | Limpia el arbol de tipado de una expresión.
cleanTypedExprTree :: IState ()
cleanTypedExprTree = getTreeExprBox >>= removeAllChildren

{- Las siguientes acciones muestran y ocultan el widget de fórmulas . -}
openFormPane :: HBox -> Paned -> IState ()
openFormPane b p = liftIO (widgetShow b >>
                           set p [ panedPositionSet := True 
                                 , panedPosition := paneFormHeight 
                                 ] >>
                           widgetShowAll p)

hidePane :: Paned -> IState ()
hidePane p = liftIO (set p [ panedPosition := 0 
                           , panedPositionSet := True ] >>
                    widgetShowAll p
                    )

openProofFace :: Notebook -> IO ()
openProofFace nt = set nt [notebookPage := 0]

openExprFace :: Notebook -> IO ()
openExprFace nt = set nt [notebookPage := 1]

addHandler :: WidgetClass w => w -> Signal EventBox (EventM any Bool) -> EventM any () -> IState (ConnectId EventBox)
addHandler eb event action = liftIO $ castToEventBox eb `on` event $ tryEvent action

configFaceSwitch :: (Notebook -> IO ()) -> Notebook -> HBox -> IRG -> IState ()
configFaceSwitch openFace nb b f = liftIO (containerGetChildren b) >>= \[eb] -> do
                                   mapM_ (uncurry (addHandler eb)) 
                                             [ (enterNotifyEvent, highlightBox b hoverBg) 
                                             , (leaveNotifyEvent, unlightBox b Nothing)
                                             ] 
                                   s <- get
                                   addHandler eb buttonPressEvent (liftIO (openFace nb) >> eventWithState f s)
                                   return ()

                           
switchToProof :: Notebook -> HBox -> IRG -> IState ()
switchToProof = configFaceSwitch openProofFace

switchToTypeTree :: Notebook -> HBox -> IRG -> IState ()
switchToTypeTree = configFaceSwitch openExprFace

{- Las siguientes acciones crean widgets como computaciones en la
mónada IState. -} 

-- | Una caja con cierto padding.
newBox :: IState HBox
newBox = liftIO (hBoxNew False 0)

newVBox :: IState VBox
newVBox = liftIO (vBoxNew False 0)

-- | Una nueva caja de texto.
newEntry :: IState Entry
newEntry = liftIO $ entryNew >>= \entry ->
           widgetModifyBase entry StateNormal grayBg >>
           return entry

-- | Una nueva etiqueta.
labelStr :: String -> IState Label
labelStr = liftIO . labelNew . return


-- | Redimensiona una caja de texto.
entryDim :: Entry -> Int -> IState ()
entryDim entry l = liftIO $ widgetSetSizeRequest entry l (-1)


-- | Pone un widget dentro de una caja.
addToBox :: (BoxClass b,WidgetClass w) => b -> w -> IRG
addToBox b w = liftIO $ boxPackStart b w PackNatural 3

-- | Elimina todos los controles contenidos en una caja (también
-- destruye los hijos para liberar memoria -- está bien hacer esto?).
removeAllChildren :: ContainerClass b => b -> IRG
removeAllChildren = liftIO . removeAllChildren'

-- | Elimina todos los controles contenidos en una caja (también
-- destruye los hijos para liberar memoria -- está bien hacer esto?).
removeAllChildren' :: ContainerClass b => b -> IO ()
removeAllChildren' b = containerForeach b $ 
                         \x -> containerRemove b x >> widgetDestroy x

{- Las siguientes funciones son los manejadores de eventos. -}




-- | Si se aprieta el botón izquierdo, empezamos a trabajar en este
-- control y luego pasamos el control a la lista de símbolos.
newFocusToSym :: IExpr' ()
newFocusToSym = getFormBox >>= \box -> 
                lift (updateFrmCtrl box) >> 
                lift (highlightBox box focusBg)

-- | Resalta todos los controles que están dentro de una caja.
highlightBox b bg = liftIO $ containerForeach b (highlight bg)

-- | Quita el resaltado a los controles que están dentro de una caja.
unlightBox b bg = liftIO $ containerForeach b (unlight bg) 

-- | Cambia el color de fondo de un control.
highlight :: WidgetClass w => Color -> w -> IO ()
highlight bg w = widgetModifyBg w (toEnum 0) bg

-- | Le quita el color especial a un control.
unlight :: WidgetClass w => (Maybe Color) -> w -> IO ()
unlight Nothing w = widgetModifyBg w (toEnum 0) genericBg
unlight (Just bg) w = widgetModifyBg w (toEnum 0) bg
    
    
fontItalic :: IO FontDescription
fontItalic = fontDescriptionNew >>= \fd ->
             fontDescriptionSetStyle fd StyleItalic >>
             return fd

-- | Setea un texto de ayuda para un widget
setToolTip :: WidgetClass w => w -> String -> IO ()
setToolTip w s = tooltipsNew >>= \t -> tooltipsSetTip t w s ""

makeButtonWithImage :: StockId -> IO Button
makeButtonWithImage s = buttonNew >>= \b ->
                        imageNewFromStock s IconSizeMenu >>=
                        containerAdd b >>
                        return b
