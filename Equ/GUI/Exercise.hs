module Equ.GUI.Exercise where

import Graphics.UI.Gtk hiding (get)

import Equ.GUI.Types
import Equ.GUI.Utils
import Equ.GUI.State
import Equ.GUI.State.Expr (getInitialExpr)
import Equ.GUI.State.Exercise 
import Equ.GUI.Widget

import Equ.Expr
import Equ.Parser (parseFromString)
import Equ.Exercise
import Equ.Exercise.Conf
import Equ.Theories (relationList, axiomGroup, Grouped (..))
import Equ.Proof.Proof(Axiom (..))
import Equ.Proof (toProof,listedToProof)
import Equ.Rule hiding (rel)

import Data.Maybe (fromJust)
import Data.Text (unpack, pack)
import Data.List (elemIndex, find)
import qualified Data.Set as S
import qualified Data.Foldable as F

import Control.Monad.State.Strict (when, get, evalStateT)

-- Configura los botones para las ventanas de configuraci´on de ejercicio y
-- enunciado.
setupExerciseToolbar :: HBox -> IState ()
setupExerciseToolbar b = do
            (exerConfButton, statementButton) <- io $ makeToolButtons
            s <- get
            io $ onToolButtonClicked exerConfButton 
                                    (evalStateT makeExerConfWindow s)
            io $ onToolButtonClicked statementButton 
                                    (evalStateT makeStatementWindow s)
            return ()
    where
        makeToolButtons :: IO (ToolButton, ToolButton)
        makeToolButtons = do
            sep <- separatorToolItemNew
            exerConfButton <- toolButtonNewFromStock stockProperties
            statementButton <- toolButtonNewFromStock stockSelectAll
            
            boxPackStart b sep PackNatural 0
            boxPackStart b exerConfButton PackNatural 0
            boxPackStart b statementButton PackNatural 0
            
            widgetSetNoShowAll b True 
            return (exerConfButton, statementButton)

-- Crear un comboBox para la configuraci´on de los campos de configuraci´on 
-- de un ejercicio.
makeExerConfComboItem :: (Show a, Eq a) => String -> ListStore a -> IState a -> 
                                           IState HBox
makeExerConfComboItem s ls isItem = do
                     box <- io $ hBoxNew False 0
                     optionLabel <- io $ labelNew $ Just s
                     
                     cbox <- io $ comboBoxNewWithModel ls
                     cellRenderer <- io $ cellRendererTextNew
                     io $ cellLayoutPackStart cbox cellRenderer True
                     io $ cellLayoutSetAttributes cbox cellRenderer ls 
                                             (\s -> [cellText := show s])
                     
                     l <- io $ listStoreToList ls
                     item <- isItem
                     io $ comboBoxSetActive cbox (fromJust $ elemIndex item l)
                     io $ boxPackStart box optionLabel PackGrow 0
                     io $ boxPackStart box cbox PackNatural 0

                     return box

-- Crea la lista de "elementos tildables" para la configuraci´on de
-- un ejercicio.
makeExerConfCheckItem :: (Show a, Eq a) => String -> [a] -> [a] -> IState HBox
makeExerConfCheckItem s items activeItems = do
                    box <- io $ hBoxNew False 0
                    optionLabel <- io $ labelNew $ Just s
                    
                    itemBox <- io $ vBoxNew False 0
                    F.mapM_ (makeExerConfCheckItem' itemBox activeItems) items
                    
                    io $ boxPackStart box optionLabel PackGrow 0
                    io $ boxPackStart box itemBox PackNatural 0
                    
                    return box

makeExerConfCheckItem' :: (Show a, Eq a, BoxClass b) => b -> [a] -> a -> IState ()
makeExerConfCheckItem' box aItems item= io $ 
                    do
                    cbutton <- checkButtonNewWithLabel $ show item
                    boxPackStart box cbutton PackNatural 0
                    when (elem item aItems)
                        (set cbutton [toggleButtonActive := True])

-- Crea los botones aceptar y cancelar para las ventanas de enunciado y 
-- configuraci´on de ejercicio.
makeOkCancelButtons :: IO HBox
makeOkCancelButtons = do
                      box <- hBoxNew False 0
                      
                      okButton <- buttonNewWithLabel "Aceptar"
                      cancelButton <- buttonNewWithLabel "Cancelar"
                      
                      boxPackEnd box cancelButton PackNatural 2
                      boxPackEnd box okButton PackNatural 2
                      
                      return box

-- Funci´on general para manejar los botones aceptar y cancelar, incluidos
-- en las ventanas de enunciado y configuraci´on de ejercicio.
setupOkCancelButtons :: HBox -> IState () -> IState () -> IState ()
setupOkCancelButtons b actionOk actionCancel = do
                [okButton, cancelButton] <- io $ containerGetChildren b
                
                s <- get 
                
                io $ onClicked (castToButton cancelButton) 
                               (flip evalStateT s $ actionCancel)
                
                io $ onClicked (castToButton okButton) 
                               (flip evalStateT s $ actionOk)
                
                return ()

-- Configuraci´on del boton aceptar para la ventana de configuraci´on de un
-- ejercicio.
actionOkButtonExerConf :: HBox -> (HBox, ListStore TypeProof) -> 
                          (HBox, ListStore RewriteMode) -> 
                          (HBox, ListStore TypeCheck) -> 
                          HBox -> [Explicit] ->
                          HBox -> Grouped Axiom -> Window -> IState ()
actionOkButtonExerConf b tpBox rwBox tcBox infoBox infoList atBox atList w = 
                    io (getActiveItemFromCombo tpBox) >>= \item ->
                    getExerciseConf >>= \exerConf ->
                    updateExerciseConf (exerConf {eConfTypeProof = item}) >>
                    
                    io (getActiveItemFromCombo rwBox) >>= \item ->
                    getExerciseConf >>= \exerConf ->
                    updateExerciseConf (exerConf {eConfRewriteMode = item}) >>
                    
                    io (getActiveItemFromCombo tcBox) >>= \item ->
                    getExerciseConf >>= \exerConf ->
                    updateExerciseConf (exerConf {eConfTypeCheck = item}) >>
                    
                    getActiveItemsFromCheckInfo infoBox infoList >>= \set ->
                    getExerciseConf >>= \exerConf ->
                    updateExerciseConf (exerConf {eConfExplicit = set}) >>

                    getActiveItemsFromCheckATheories atBox atList >>= \ls ->
                    getExerciseConf >>= \exerConf ->
                    updateExerciseConf (exerConf {eConfAvaibleTheories = ls}) >>
                    
                    io (widgetDestroy w)

-- Retorna el conjunto de teorias disponibles.
getActiveItemsFromCheckATheories :: HBox -> Grouped Axiom -> IState (Grouped Axiom)
getActiveItemsFromCheckATheories b gAxiom = do
                            [_, itemBox] <- io $ containerGetChildren b
                            itemList <- io $ containerGetChildren (castToBox itemBox)
                            getActiveItemsFromCheck' itemList gAxiom []
    where 
        getActiveItemsFromCheck' :: [Widget] -> Grouped Axiom -> Grouped Axiom -> 
                                    IState (Grouped Axiom)
        getActiveItemsFromCheck' [] _ ga = return ga
        getActiveItemsFromCheck' (cbutton:cbuttons) ilist ga = do
                    act <- io $ toggleButtonGetActive (castToToggleButton cbutton)
                    case act of
                            False -> getActiveItemsFromCheck' cbuttons ilist ga
                            True -> io (buttonGetLabel (castToButton cbutton)) >>= \l ->
                                    getItemFromList l >>= \item -> 
                                    getActiveItemsFromCheck' cbuttons ilist (item : ga)
            where
                getItemFromList s = return $ fromJust $ find (\i -> s == show (fst i)) ilist

-- Retorna el conjunto de items seleccionado para mostrar como informaci´on
-- relacionado a la configuraci´on de un ejercicio.
getActiveItemsFromCheckInfo :: HBox -> [Explicit] -> IState (S.Set Explicit)
getActiveItemsFromCheckInfo b infoList = do
                            [_, itemBox] <- io $ containerGetChildren b
                            itemList <- io $ containerGetChildren (castToBox itemBox)
                            getActiveItemsFromCheck' itemList infoList S.empty
    where 
        getActiveItemsFromCheck' :: [Widget] -> [Explicit] -> S.Set Explicit -> 
                                    IState (S.Set Explicit)
        getActiveItemsFromCheck' [] _ s = return s
        getActiveItemsFromCheck' (cbutton:cbuttons) ilist s = do
                    act <- io $ toggleButtonGetActive (castToToggleButton cbutton)
                    case act of
                            False -> getActiveItemsFromCheck' cbuttons ilist s
                            True -> io (buttonGetLabel (castToButton cbutton)) >>= \l ->
                                    getItemFromList l >>= \item -> 
                                    getActiveItemsFromCheck' cbuttons ilist (S.insert item s)
            where
                getItemFromList :: String -> IState Explicit
                getItemFromList s = return $ fromJust $ find (\i -> s == show i) ilist

-- Item activo en un comboBox.
getActiveItemFromCombo :: (Show a, BoxClass b) => (b, ListStore a) -> IO a
getActiveItemFromCombo (b, ls) = do
                        [_, cBox] <- containerGetChildren b
                        i <- comboBoxGetActive (castToComboBox cBox)
                        item <- listStoreGetValue ls i
                        return item

-- Crea una ventana que permite editar los campos para la configuraci´on de
-- un ejercicio.
makeExerConfWindow :: IState ()
makeExerConfWindow = do
                     vBox <- newVBox
                     
                     tpLs <- io $ listStoreNew typeProofOptionList
                     tpBox <- makeExerConfComboItem "Tipo de prueba" tpLs
                                   getExerciseConfTypeProof
                     vBoxAdd vBox tpBox
                     
                     rwLs <- io $ listStoreNew rewriteModeOptionList
                     rwBox <- makeExerConfComboItem "Re-escritura" rwLs
                                   getExerciseConfRewriteMode
                     vBoxAdd vBox rwBox 
                     
                     tcLs <- io $ listStoreNew typeCheckOptionList 
                     tcBox <- makeExerConfComboItem "Chequeo de tipos" tcLs
                                   getExerciseConfTypeCheck
                     vBoxAdd vBox tcBox
                    
                     explicitInfo <- getExerciseConfExplicitInfo
                     infoBox <- makeExerConfCheckItem 
                                                    ("Información a mostrar" 
                                                    ++ "\n" 
                                                    ++ "sobre el objetivo" )
                                                    explicitOptionList
                                                    (S.toList explicitInfo)
                     vBoxAdd vBox infoBox
                     
                     aTheories <- getExerciseConfATheories
                     atBox <- makeExerConfCheckItem 
                                                    "Axiomas Disponibles" 
                                                    (map fst axiomGroup)
                                                    (map fst aTheories)
                     vBoxAdd vBox atBox
                     
                     box <- io $ makeOkCancelButtons
                     io $ boxPackEnd vBox box PackNatural 2
                     
                     w <- makeWindowPop vBox 300
                     
                     setupOkCancelButtons box 
                        (actionOkButtonExerConf box (tpBox, tpLs) (rwBox, rwLs) 
                                                (tcBox, tcLs) 
                                                infoBox explicitOptionList 
                                                atBox axiomGroup w)
                        (io $ widgetDestroy w)
    where
        vBoxAdd :: WidgetClass w => VBox -> w -> IState ()
        vBoxAdd vBox w = do
                         io $ boxPackStart vBox w PackNatural 2
                         sep <- io $ hSeparatorNew
                         io $ boxPackStart vBox sep PackNatural 2

-- Crea un entry para ingresar el texto relacionado a un titulo del enunciado.
makeExerciseTitleEntry :: IState HBox
makeExerciseTitleEntry = do
                    box <- io $ hBoxNew False 0
                    
                    optionLabel <- io $ labelNew $ Just "Titulo"
                    
                    stat <- getExerciseStatement
                    entry <- io $ entryNew
                    io $ entrySetText entry $ (unpack . title) stat
                    
                    io $ boxPackStart box optionLabel PackGrow 0
                    io $ boxPackStart box entry PackNatural 0
                    
                    return box

-- Crea un textview para ingresar texto relacionado con los hint's del
-- enunciado.
makeExerciseHintEntry :: IState HBox
makeExerciseHintEntry = do
                    box <- io $ hBoxNew False 0
                    
                    optionLabel <- io $ labelNew $ Just "Hint's"
                    
                    stat <- getExerciseStatement
                    
                    textView <- io $ textViewNew
                    io $ textViewSetWrapMode textView WrapWord
                    io $ set textView [ widgetWidthRequest := 200
                                      , widgetHeightRequest := 100
                                      ]
                    
                    textBuffer <- io $ textViewGetBuffer textView
                    
                    io $ textBufferSetText textBuffer (unpack $ hints stat)
                    
                    io $ boxPackStart box optionLabel PackGrow 0
                    io $ boxPackStart box textView PackNatural 0
                    
                    return box

-- Acci´on del boton Aceptar para la ventana de edici´on del enunciado.
actionOkButtonStatement :: HBox -> HBox -> Window -> IState ()
actionOkButtonStatement titleBox hintBox w = do
                     
                     updateExerciseStatementTitle titleBox
                     
                     updateExerciseStatementHint hintBox
                     
                     io (widgetDestroy w)

-- Update del titulo de un enunciado.
updateExerciseStatementTitle :: HBox -> IState ()
updateExerciseStatementTitle titleBox = do
                            [_,entry] <- io $ containerGetChildren titleBox
                            text <- io $ entryGetText (castToEntry entry)
                            stat <- getExerciseStatement
                            updateExerciseStatement (stat {title = pack text})

-- Update del hint de un enunciado.
updateExerciseStatementHint :: HBox -> IState ()
updateExerciseStatementHint hintBox = do
            [_,textView] <- io $ containerGetChildren hintBox
            textBuffer <- io $ textViewGetBuffer (castToTextView textView)
            textIterStart <- io $ textBufferGetStartIter textBuffer
            textIterEnd <- io $ textBufferGetEndIter textBuffer
            
            text <- io $ textBufferGetText textBuffer 
                                           textIterStart 
                                           textIterEnd False
            
            stat <- getExerciseStatement
            updateExerciseStatement (stat {hints = pack text})

-- Crea una ventana que permite editar los campos de un enunciado.
makeStatementWindow :: IState ()
makeStatementWindow =  do
                     vBox <- newVBox
                     
                     titleBox <- makeExerciseTitleEntry
                     vBoxAdd vBox titleBox
                     
                     hintBox <- makeExerciseHintEntry
                     vBoxAdd vBox hintBox
                     
                     box <- io $ makeOkCancelButtons
                     io $ boxPackEnd vBox box PackNatural 2
                     
                     w <- makeWindowPop vBox 400
                     
                     setupOkCancelButtons box 
                        (actionOkButtonStatement titleBox hintBox w)
                        (io $ widgetDestroy w)
    where
        vBoxAdd :: WidgetClass w => VBox -> w -> IState ()
        vBoxAdd vBox w = do
                         io $ boxPackStart vBox w PackNatural 2
                         sep <- io $ hSeparatorNew
                         io $ boxPackStart vBox sep PackNatural 2

-- Asocia una prueba a un ejercicio. Esta funci´on esta proxima a cambiar
-- bastante debido a que la asociacion se hara durante el guardado del
-- ejercicio.
makeAssocProofWindow :: IState ()
makeAssocProofWindow = do
            proofState <- getProofState
            case proofState of
                Nothing -> makeErrWindow 
                           "No existe prueba para asociar al ejercicio. "
                Just ps -> getExercise >>= \(Just exer) ->
                           updateExercise $ 
                                exer {exerProof = Just $ listedToProof $ proof ps }

-- Genera una ventana para mostar el contenido de "b" con ancho width
makeWindowPop :: (BoxClass b) => b -> Int -> IState Window
makeWindowPop box width = io $ 
                    do
                    w <- windowNew
                    containerAdd w box
                    set w [windowDefaultWidth := width]
                    windowSetPosition w WinPosCenterAlways
                    widgetShowAll w
                    return w

-- Guarda un ejercicio.
saveExercise :: IState ()
saveExercise = return ()

-- Crea un ejercicio.
makeExercise :: IState ()
makeExercise = getInitialExpr >>= updateExercise . initExercise . fromJust
    where
        initExercise :: Expr -> Exercise
        initExercise = createExercise
