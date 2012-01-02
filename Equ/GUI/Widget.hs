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

-- | Reportar errores usando la panel de errores. Toma un mensaje de error y 
-- lo muestra en el panel. TODO: Que pasa si el string es muuuuuy largo. 
reportErrWithErrPaned :: String -> IState ()
reportErrWithErrPaned s = setErrMessage s >>
                          openErrPane


-- | Reportar resultados exitosos en la consola.
reportSuccess :: String -> IState ()
reportSuccess = liftIO . putStrLn


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


-- Elimina todos los widget's de una contenedor.
cleanContainer :: (ContainerClass c) => c -> IState ()
cleanContainer c = liftIO (containerForeach c $ containerRemove c)

-- | Limpia el arbol de tipado de una expresión.
cleanTypedExprTree :: IState ()
cleanTypedExprTree = getTreeExprBox >>= \bTree -> cleanContainer bTree

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
newEntry = liftIO entryNew

-- | Una nueva etiqueta.
labelStr :: String -> IState Label
labelStr = liftIO . labelNew . return


-- | Redimensiona una caja de texto.
entryDim :: Entry -> Int -> IState ()
entryDim entry l = liftIO $ widgetSetSizeRequest entry l (-1)


-- | Pone un widget dentro de una caja.
addToBox :: (BoxClass b,WidgetClass w) => b -> w -> IRG
addToBox b w = liftIO $ boxPackStart b w PackGrow 0

-- | Elimina todos los controles contenidos en una caja (también
-- destruye los hijos para liberar memoria -- está bien hacer esto?).
removeAllChildren :: BoxClass b => b -> IRG
removeAllChildren b = liftIO $ containerForeach b $ 
                         \x -> containerRemove b x >> widgetDestroy x

-- | Poné en una caja el widget que usamos para construir nuevas
-- expresiones.
setupForm ::  HBox -> IRG
setupForm b = labelStr "?" >>= \l -> setupFormEv b l holePreExpr

-- | Asigna los manejadores de eventos para widgets de expresiones a 
-- los controles.
setupFormEv :: WidgetClass w => HBox -> w -> PreExpr -> IRG
setupFormEv b c e = liftIO eventBoxNew >>= \eb ->
                    addToBox b eb >>
                    liftIO (set eb [ containerChild := c ]) >>
                    setupEvents b eb e

-- | Define los manejadores de eventos para una caja que tiene el
-- widget para construir expresiones.
setupEvents :: WidgetClass w => HBox -> w -> PreExpr -> IRG
setupEvents b eb e = get >>= \s ->
                     getPath >>= \p ->
                     getSymCtrl >>= \sym ->
                     addHandler eb enterNotifyEvent (highlightBox b hoverBg) >>
                     addHandler eb leaveNotifyEvent (unlightBox b Nothing) >>
                     addHandler eb buttonPressEvent (newFocusToSym b p sym s) >>
                     addHandler eb buttonPressEvent (removeExpr b s) >>
                     return ()
    where newExpr = ExprState (toFocus e) TyUnknown (id,id) b b

{- Las siguientes funciones son los manejadores de eventos. -}

-- | Si apretamos el botón derecho, entonces borramos la expresión
-- enfocada.
removeExpr :: HBox -> GRef -> EventM EButton ()
removeExpr b s = do RightButton <- eventButton
                    eventWithState (updateExpr holePreExpr >>
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
                                             openSymFrame) s
                             liftIO $ highlightBox l focusBg
                             -- liftIO $ widgetGrabFocus sym
                             return ()

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


-- | Funcion para mostrar dialogo con mensaje de error
errorDialog :: String -> IO ()
errorDialog message = do
    dialog <- dialogNew
    set dialog [windowTitle := "Error"]
    box <- dialogGetUpper dialog
    label <- labelNew $ Just message
    boxPackStart box label PackNatural 2
    
    dialogAddButton dialog stockApply ResponseApply
        
    widgetShowAll box
   
    dialogRun dialog
    widgetDestroy dialog
    

{- Conjunto de funciones para cargar y guardar una lista de expresiones.
    Esto es una prueba no mas de lo que podemos llegar a querer hacer con
    las pruebas.
    ESTO ESTA SUPER MAL ACÁ, EN ESTE MODULO.
-}
-- exprListFile :: FilePath
-- exprListFile = "Saves/FormList"
-- 
-- pseudoProofFile :: FilePath
-- pseudoProofFile = "Saves/FormList"
-- 
-- saveDummyProof :: IState ()
-- saveDummyProof = getExprListFromProof >>= 
--                 \l -> liftIO $ encodeFile pseudoProofFile $ map (\(TypedExpr e t _ _ _) -> (e,t)) l
-- 
-- loadDummyProof :: VBox -> IState ()
-- loadDummyProof b = liftIO (decodeFile pseudoProofFile) >>= loadDummyProof' b
-- 
-- loadDummyProof' :: VBox -> [(Focus, Type)] -> IState ()
-- loadDummyProof' b [] = liftIO $ containerGetChildren b >>= \(e:es) -> containerRemove b e >> return ()
-- loadDummyProof' b ((f,t):es) =  get >>= \s -> setupEventExpr f t >>= \(eb, tb) ->
--                                 labelStr "≡ \t\t\t\t [AXIOMA/TEOREMA]" >>= \l ->
--                                 liftIO (boxPackStart b l PackNatural 2) >>
--                                 liftIO (boxPackStart b eb PackNatural 2) >>
--                                 liftIO (widgetShowAll b) >>
--                                 liftIO (configEventSelectExprFromProof eb s) >>
--                                 addExprToProof f eb tb >>
--                                 loadDummyProof' b es
-- 
-- saveFormList :: IState ()
-- saveFormList = getTypedFormList >>= 
--                \l -> liftIO $ encodeFile exprListFile $ map (\(TypedExpr e t _ _ _) -> (e,t)) l
-- 
-- loadFormList :: IState ()
-- loadFormList = liftIO (decodeFile exprListFile) >>= loadFormList'
-- 
-- loadFormList' :: [(Focus, Type)] -> IState ()
-- loadFormList' [] = return ()
-- loadFormList' ((f,t):es) = get >>= \s -> getTypedFormBox >>=
--                        \b -> setupEventExpr f t >>= \(eb, tb) ->
--                        liftIO (boxPackStart b eb PackNatural 2) >>
--                        liftIO (widgetShowAll eb) >>
--                        liftIO (configEventSelectExprFromList eb s) >>
--                        addExprToList f eb tb >>
--                        loadFormList' es
-- 
-- encodeFile :: S.Serialize a => FilePath -> a -> IO ()
-- encodeFile f v = L.writeFile f (S.encode v)
-- 
-- decodeFile :: S.Serialize a => FilePath -> IO a
-- decodeFile f = do s <- L.readFile f
--                   either (error) (return) $ S.runGet (do v <- S.get
--                                                          m <- S.isEmpty
--                                                          m `seq` return v) s
-- 
