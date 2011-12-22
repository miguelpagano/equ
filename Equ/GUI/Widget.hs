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

-- | Abre el panel de error.
openErrPane :: IState ()
openErrPane = getFormErrPane >>= \erp ->
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
closeErrPane = getFormErrPane >>= \erp ->
              liftIO (set erp [ panedPositionSet := True 
                              , panedPosition := 0 ] >>
                      widgetShowAll erp)

-- Función principal que construye el arbol de tipado.
buildTypedFormTree :: ExprState -> IState ()
buildTypedFormTree te = get >>= \s ->
                        getBoxTypedFormTree >>= \bTree -> 
                        setupEventExpr (fExpr te) (fType te) >>= 
                        \(eb, tb) -> newBox >>=
                        \bb -> 
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

buildTypedFormTree' :: (BoxClass b) => ExprState -> b -> IState ()
buildTypedFormTree' te bTree = 
                    do
                    goDownLTe <- goDownLTypedExpr te
                    goDownRTe <- goDownRTypedExpr te
                    case (goDownLTe, goDownRTe) of
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
configEventGeneralExpr eb b = do 
                    (eb `on` enterNotifyEvent $ tryEvent $ 
                                                highlightBox b hoverBg)
                    (eb `on` leaveNotifyEvent $ tryEvent $ unlightBox b genericBg)
                    return ()

configEventSelectExprFromTree :: HBox -> GRef -> IO ()
configEventSelectExprFromTree b s = containerGetChildren b >>= \[eb] ->
                        do
                        eb `on` buttonPressEvent $ tryEvent $ 
                                eventWithState (selectExprFromBox b >> 
                                                openTypedOptionPane) s
                        return ()

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
                                                cleanTypedFormPane >>
                                                cleanTreeExpr >>
                                                getSelectExpr >>= \(Just te) ->
                                                buildTypedFormTree te >>
                                                return ()) >> 
                                return ()
-- 
-- typedCheckType :: IState ()
-- typedCheckType = getTypedSelectExpr >>= \(Just te) ->
--                  case checkPreExpr (fst . typedExpr $ te) of
--                       Left err -> (reportErrWithErrPaned $ show err)
--                       Right checkType ->
--                         if checkType == (typedType te) then
--                             liftIO (highlightBox (eventType te) focusBg >> 
--                                     widgetShowAll (eventType te))
--                         else 
--                             get >>= \s ->
--                             liftIO (configEventCheckType (eventType te) checkType s)
--                             
-- 
-- configEventCheckType :: HBox -> Type -> GRef -> IO ()
-- configEventCheckType b t s = labelNew (Just $ show t) >>= 
--                             \typeL -> labelNew (Just $ "Vs") >>= 
--                              \vsL -> eventBoxNew >>= \typeEb -> 
--                              set typeEb [containerChild := typeL] >>
--                              set b [containerChild := vsL] >>
--                              set b [containerChild := typeEb] >>
--                              highlightBox b errBg >> 
--                              widgetShowAll b >>
--                              (typeEb `on` buttonPressEvent $ tryEvent $ 
--                                           eventWithState (
--                                           liftIO (containerRemove b vsL >> 
--                                                   containerRemove b typeEb >> 
--                                                   widgetShowAll b)) s) >> 
--                               return ()

checkInExpr :: String -> IState (Maybe PreExpr)
checkInExpr s = case parseFromString s of
                        Left err -> (reportErrWithErrPaned $ show err) >> return Nothing
                        Right expr -> return $ Just expr

checkInType :: String -> IState (Maybe Type)
checkInType s = case parseTyFromString s of
                     Left err -> reportErrWithErrPaned (show err) >> return Nothing
                     Right t -> return $ Just t

goDownLTypedExpr :: ExprState -> IState (Maybe (ExprState, HBox, HBox))
goDownLTypedExpr te = goTypedExpr (goDownL) te

goDownRTypedExpr :: ExprState -> IState (Maybe (ExprState, HBox, HBox))
goDownRTypedExpr te = goTypedExpr (goDownR) te

goTypedExpr :: (Focus -> Maybe Focus) -> ExprState -> IState (Maybe (ExprState, HBox, HBox))
goTypedExpr go te = 
            case (go . fExpr) te of
                Nothing -> return Nothing
                Just f ->   get >>= \s -> setupEventExpr f TyUnknown >>= \(eb,tb) -> 
                            liftIO (configEventSelectExprFromTree eb s) >>
                            liftIO (configEventSelectTypeFromTree tb s) >>
                            addExprToTree f TyUnknown 
                                          (fromJust . (go . (fst . pathExpr $ te)), fromJust . (go . (snd . pathExpr $ te)))
                                          eb tb >>= 
                            \te' -> return $ Just (te', eb, tb)

typedExprInEdit :: IState ()
typedExprInEdit = getSelectExpr >>= \(Just te) -> 
                  do
                  b <- return $ eventExpr te
                  [eb] <- liftIO $ containerGetChildren b
                  eText <- liftIO $ entryNew
                  liftIO (entrySetText eText (show (fst . fExpr $ te)) >>
                          containerRemove (castToBox b) eb >>
                          boxPackStart b eText PackGrow 0 >> 
                          widgetShowAll b)
                  configExprEntry eText b te

setupEventExpr :: Focus -> Type -> IState (HBox, HBox)
setupEventExpr (e,_) t = liftIO $
                            do 
                                exprL <- (labelNew $ Just $ show e)
                                typeL <- (labelNew $ Just $ show t)
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

-- Elimina todos los widget's de una contenedor.
cleanContainer :: (ContainerClass c) => c -> IState ()
cleanContainer c = liftIO (containerForeach c $ containerRemove c)

-- | Limpia el arbol de tipado de una expresión.
cleanTypedFormPane :: IState ()
cleanTypedFormPane = getBoxTypedFormTree >>= \bTree -> cleanContainer bTree

{- Las siguientes acciones muestran y ocultan el widget de fórmulas . -}
openFormPane :: HBox -> Paned -> IState ()
openFormPane b p = liftIO (widgetShow b >>
                           set p [ panedPositionSet := True 
                                 , panedPosition := paneFormHeight 
                                 ] >>
                           widgetShowAll p)

hidePane :: HBox -> Paned -> IState ()
hidePane b p = liftIO (widgetHide b >>
                           set p [ panedPosition := 0 
                                 , panedPositionSet := True ] >>
                           widgetShowAll p
                           )

-- | Abre el menu de opciones para las expresiones ingresadas.
-- TODO: Faltaría prestar atención a los valores necesarios para hacer
-- las definiciones correctas de las posiciones.
openTypedOptionPane :: IState ()
openTypedOptionPane = getExprOptionPane >>= 
                      \p ->liftIO (set p [ panedPositionSet := True 
                                         , panedPosition := 1300
                                         ] >>
                                   widgetShowAll p
                                  )

-- | Igual que arriba pero para cerrar el panel.
hideTypedOptionPane :: IState ()
hideTypedOptionPane = getExprOptionPane >>= 
                      \p -> liftIO (set p [ panedPosition := 2000
                                          , panedPositionSet := True ] >>
                                    widgetShowAll p
                                   )

openProofFace :: Notebook -> IO ()
openProofFace nt = set nt [notebookPage := 0]

openExprFace :: Notebook -> IO ()
openExprFace nt = set nt [notebookPage := 1]

configArrowToProof :: Notebook -> HBox -> IState ()
configArrowToProof p b = liftIO (containerGetChildren b) >>= \[eb] ->
                         liftIO ((castToEventBox eb) `on` enterNotifyEvent $ tryEvent $ highlightBox b hoverBg) >>
                         liftIO ((castToEventBox eb) `on` leaveNotifyEvent $ tryEvent $ unlightBox b genericBg) >>
                         liftIO ((castToEventBox eb) `on` buttonPressEvent $ tryEvent $ liftIO $ openProofFace p) >>
                         return ()
                           

configArrowToExpr :: Notebook -> HBox -> IState ()
configArrowToExpr p b = liftIO (containerGetChildren b) >>= \[eb] ->
                        liftIO ((castToEventBox eb) `on` enterNotifyEvent $ tryEvent $ (highlightBox b hoverBg >> return ())) >>
                        liftIO ((castToEventBox eb) `on` leaveNotifyEvent $ tryEvent $ unlightBox b genericBg) >>
                        liftIO ((castToEventBox eb) `on` buttonPressEvent $ tryEvent $ liftIO $ openExprFace p) >>
                        return ()

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
setupForm b = labelStr "?" >>= \l -> setupFormEv b l holeExpr

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
setupEvents b eb e = do s <- get
                        p <- getPath
                        sym <- getSymCtrl
                        liftIO $ eb `on` enterNotifyEvent $ tryEvent $ highlightBox b hoverBg
                        liftIO $ eb `on` leaveNotifyEvent $ tryEvent $ unlightBox b genericBg
                        liftIO $ eb `on` buttonPressEvent $ tryEvent $ 
                                        (newFocusToSym b p sym s >> 
                                         eventWithState (
                                                        (updateExprState (ExprState 
                                                                            (toFocus e) 
                                                                            TyUnknown (id,id) 
                                                                            b b) )
                                                         ) s
                                         )
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
                                             openSymFrame) s
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
