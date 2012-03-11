-- | Aspectos de la interfaz independientes de las expresiones.
module Equ.GUI.Widget where

import Equ.PreExpr
import Equ.Parser
import Equ.TypeChecker
import Equ.Types
import Equ.Rule
import Equ.Theories
import Equ.Proof hiding (goDownL, goDownR)


import Equ.GUI.Types
import Equ.GUI.State
import Equ.GUI.State.Expr
import Equ.GUI.State.SymbolList
import Equ.GUI.Utils
import Equ.GUI.Settings


import Graphics.UI.Gtk hiding (eventButton, eventSent,get)
import qualified Graphics.UI.Gtk as G
import Graphics.UI.Gtk.Gdk.EventM
import Graphics.UI.Gtk.Glade (GladeXML,xmlGetWidget)
import Data.Reference
import Data.Text(unpack)
import Data.List (deleteBy)

import qualified Data.Foldable as F
import Control.Monad.Trans(lift,liftIO)
import Control.Monad.Reader(ask)
import Control.Monad.State(get,evalStateT)
import Control.Monad(filterM) 

import qualified Data.Serialize as S
import qualified Data.ByteString as L

import Graphics.Rendering.Pango.Font

tooltipF :: (WidgetClass w ,TooltipClass self) => w -> self  -> IO Bool
tooltipF w t = (hBoxNew False 0) >>= \box ->
               labelNew (Just "Hola") >>= \lbl ->
               boxPackStart box lbl PackNatural 3 >>
               widgetShowAll box >>
               putStrLn "bbbb" >>
               tooltipSetCustom t (Just lbl) >>             
               widgetGetTooltipWindow w >>= \ win ->
               windowPresent win >>
               return True

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
labelStr s = io (labelNew (return s) >>= \ lbl ->
                 set lbl [ widgetHasTooltip := True ] >>
                 newTTwin >>= \win ->
                 widgetSetTooltipWindow lbl (Just win) >>
                 on lbl queryTooltip (\w p t -> windowPresent win >> return True) >>
                 widgetTriggerTooltipQuery lbl >>
                 return lbl)


newTTwin = windowNewPopup >>= \win ->
           widgetSetName win "gtk-tooltip" >>
           return win

-- | Redimensiona una caja de texto.
entryDim :: Entry -> Int -> IState ()
entryDim entry l = liftIO $ widgetSetSizeRequest entry l (-1)


-- | Pone un widget dentro de una caja.
addToBox :: (BoxClass b,WidgetClass w) => b -> w -> IRG
addToBox b w = liftIO $ boxPackStart b w PackNatural 3

-- | Elimina todos los controles contenidos en una caja (también
-- destruye los hijos para liberar memoria -- está bien hacer esto?).
removeAllChildren :: ContainerClass b => b -> IRG
removeAllChildren = io . removeAllChildren' 

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
                ask >>= \env ->
                lift getSymCtrl >>= \symbols ->
                lift getSymStore >>= \sListStore ->
                lift (runEnv (eventsSymbolList symbols sListStore) env) >>
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
    
    

-- | Setea un texto de ayuda para un widget
setToolTip :: WidgetClass w => w -> String -> IO ()
setToolTip w s = tooltipsNew >>= \t -> tooltipsSetTip t w s ""

makeButtonWithImage :: StockId -> IO Button
makeButtonWithImage s = buttonNew >>= \b ->
                        imageNewFromStock s IconSizeMenu >>=
                        containerAdd b >>
                        return b

showAllItemTool :: WidgetClass w => w -> IState ()
showAllItemTool tb = io $ 
                    do
                    widgetSetNoShowAll tb False 
                    widgetShowAll tb
                       
hideExerItemTool :: HBox -> IState ()
hideExerItemTool tb = io $
                    do
                    widgetSetNoShowAll tb True
                    widgetHideAll tb

makeErrWindow :: String -> IState ()
makeErrWindow s = io $ 
        do
        md <- messageDialogNew Nothing [DialogModal] MessageError ButtonsOk s
        widgetShowAll md
        response <- dialogRun md
        case response of
            _ -> widgetDestroy md

-- Abre una ventana para cargar un tipo con instancia Serialize, retorna True
-- si la opci´on fue cargar, retorna False si la opci´on fue cancelar.
dialogLoad :: (S.Serialize s) => String -> (FileChooserDialog -> IO ()) -> 
                               (s -> IO ()) -> IO Bool
dialogLoad label fileFilter action = do
    dialog <- fileChooserDialogNew (Just label) 
                                    Nothing 
                                    FileChooserActionOpen
                                    [ ("Cargar",ResponseAccept)
                                    , ("Cancelar",ResponseCancel)]

    fileFilter dialog 
    response <- dialogRun dialog
    
    case response of
        ResponseAccept -> do
            selected <- fileChooserGetFilename dialog
            flip F.mapM_ selected (\filepath -> 
                                    decodeFile filepath >>= \decode ->
                                    action decode >>
                                    widgetDestroy dialog)
            return True
        _ -> widgetDestroy dialog >> return False

-- Abre una ventana para guardar un tipo con instancia Serialize, retorna True 
-- si la opci´on fue guardar, retorna False si la opci´on fue cancelar.
saveDialog :: (S.Serialize s) => String -> String ->
                                 (FileChooserDialog -> IO ()) -> 
                                 s -> IState Bool
saveDialog label filename fileFilter serialItem = do
    dialog <- io $ fileChooserDialogNew (Just label) 
                                        Nothing 
                                        FileChooserActionSave 
                                        [ ("Guardar",ResponseAccept)
                                        , ("Cancelar",ResponseCancel)]
    
    io $ fileChooserSetCurrentName dialog filename
    io $ fileFilter dialog
    response <- io $ dialogRun dialog

    case response of
        ResponseAccept -> io (fileChooserGetFilename dialog) >>= 
                          \fp -> F.mapM_ save fp >> 
                          io (widgetDestroy dialog) >> return True
        _ -> io (widgetDestroy dialog) >> return False
    where
        save:: FilePath -> IState ()
        save filepath = io $ encodeFile filepath serialItem

-- Genera una ventana para mostar el contenido de "b" con ancho width
makeWindowPop :: (BoxClass b) => b -> Int -> Bool -> IState Window
makeWindowPop box width isModal = io $ 
                    do
                    w <- windowNew
                    containerAdd w box
                    set w [ windowDefaultWidth := width
                          , windowModal := isModal
                          ]
                    windowSetPosition w WinPosCenterAlways
                    widgetShowAll w
                    return w


popupWin :: Window -> IO Window
popupWin w = windowNew >>= \pop ->
             set pop  [ windowDecorated := False
                      , windowHasFrame := False
                      , windowTypeHint := WindowTypeHintDialog
                      , windowTransientFor := w
                      , windowGravity := GravityCenter
                      , windowOpacity := 0.8
                      ] >>
             windowSetPosition pop WinPosCenterAlways >>
             return pop
             
             
                        
unSelectBox :: IRG      
unSelectBox = getStepProofBox >>= F.mapM_ (\box -> unlightBox box (Just axiomBg))

selectBox :: Color -> IRG
selectBox color = getStepProofBox >>= F.mapM_ (\box -> highlightBox box color)



changeProofFocusAndShow ind = getSelIndexProof >>= \i ->
                              if i==ind
                                 then return ()
                                 else unSelectBox >>
                                      changeProofFocus ind >>
                                      selectBox focusBg >>
                                      getExprWidget >>= \ew -> 
                                      getSymCtrl >>= \symbols ->
                                      getSymStore >>= \sListStore ->
                                      runEnvBox (eventsSymbolList symbols sListStore) (ew,id,ind)
             
