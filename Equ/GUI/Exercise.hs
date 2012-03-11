{-# Language OverloadedStrings #-}
module Equ.GUI.Exercise where

import Graphics.UI.Gtk hiding (get)

import Equ.GUI.Types
import Equ.GUI.Utils
import Equ.GUI.State
import Equ.GUI.Expr (initExprState)
import Equ.GUI.State.Expr (getInitialExpr)
import Equ.GUI.Proof (createNewProof,discardProof)
import Equ.GUI.TruthList
import Equ.GUI.State.Exercise 
import Equ.GUI.Widget

import Equ.Expr (Expr, getPreExpr)
import Equ.PreExpr(toFocus)
import Equ.Parser (parseFromString)
import Equ.Exercise
import Equ.Exercise.Conf
import Equ.Theories (relationList, axiomGroup, Grouped (..), theoriesInGroup)
import Equ.Proof.Proof(Axiom (..))
import Equ.Proof (ProofAnnotation,Proof,toProof, goTop, toProofFocus)
import Equ.Proof.ListedProof
import Equ.Rule hiding (rel)

import qualified Graphics.UI.Gtk as G

import Data.Maybe (fromJust,isJust)
import Data.Text (Text,unpack, pack)
import Data.List (elemIndex, find)

import qualified Data.Set as S
import qualified Data.Foldable as F

import Control.Monad.State.Strict (when, get, evalStateT)
import Control.Monad.IO.Class (MonadIO)

-- Configura los botones para las ventanas de configuraci´on de ejercicio y
-- enunciado.
setupExerciseEditToolbar :: Toolbar -> IState ()
setupExerciseEditToolbar b = do
            (exerConfButton, statementButton) <- io makeToolButtons
            s <- get
            io $ onToolButtonClicked exerConfButton 
                                    (evalStateT makeExerConfWindow s)
            io $ onToolButtonClicked statementButton 
                                    (evalStateT makeStatementEditWindow s)
            return ()
    where
        makeToolButtons :: IO (ToolButton, ToolButton)
        makeToolButtons = do
            sep <- separatorToolItemNew
            exerConfButton <- toolButtonNewFromStock stockProperties
            statementButton <- toolButtonNewFromStock stockSelectAll
            toolButtonSetLabel exerConfButton (Just "Configuración")
            toolButtonSetLabel statementButton (Just "Enunciado")
            toolbarInsert b exerConfButton 0
            toolbarInsert b statementButton 1
            
            widgetSetNoShowAll b True 
            return (exerConfButton, statementButton)

setupExerciseToolbar :: Toolbar -> IState ()
setupExerciseToolbar b = do
                    statementButton <- io makeToolButtons
                    s <- get
                    io $ onToolButtonClicked statementButton
                                            (evalStateT makeStatementWindow s)
                    return ()
    where
        makeToolButtons :: IO (ToolButton)
        makeToolButtons = do
            sep <- separatorToolItemNew
            statementButton <- toolButtonNewFromStock stockSelectAll
            toolButtonSetLabel statementButton (Just "Enunciado")
            toolbarInsert b statementButton 0
            
            widgetSetNoShowAll b True
            return statementButton

-- Crear un comboBox para la configuraci´on de los campos de configuraci´on 
-- de un ejercicio.
makeExerConfComboItem :: (Show a, Eq a) => String -> ListStore a -> IState a -> 
                                           IState HBox
makeExerConfComboItem s ls isItem = do
                     box <- io $ hBoxNew False 0
                     optionLabel <- io $ labelNew $ Just s
                     
                     cbox <- io $ comboBoxNewWithModel ls
                     cellRenderer <- io cellRendererTextNew
                     io $ cellLayoutPackStart cbox cellRenderer True
                     io $ cellLayoutSetAttributes cbox cellRenderer ls 
                                             (\s -> [cellText := show s])
                     
                     l <- io $ listStoreToList ls
                     item <- isItem
                     io $ comboBoxSetActive cbox (fromJust $ elemIndex item l)
                     io $ set optionLabel [ widgetWidthRequest := 240 ]
                     io $ boxPackStart box optionLabel PackNatural 10
                     io $ boxPackStart box cbox PackNatural 10

                     return box

-- Crea la lista de "elementos tildables" para la configuraci´on de
-- un ejercicio.
makeExerConfCheckItem :: (Show a, Eq a) => String -> [a] -> [a] -> IState HBox
makeExerConfCheckItem s items activeItems = do
                    box <- io $ hBoxNew False 0
                    optionLabel <- io $ labelNew $ Just s
                    
                    itemBox <- io $ vBoxNew False 0
                    F.mapM_ (makeExerConfCheckItem' itemBox activeItems) items
                    
                    io $ boxPackStart box optionLabel PackNatural 10
                    io $ set optionLabel [ widgetWidthRequest := 240 ]
                    io $ boxPackStart box itemBox PackNatural 10
                    
                    return box

makeExerConfCheckItem' :: (Show a, Eq a, BoxClass b) => b -> [a] -> a -> IState ()
makeExerConfCheckItem' box aItems item= io $ 
                    do
                    cbutton <- checkButtonNewWithLabel $ show item
                    boxPackStart box cbutton PackNatural 0
                    when (item `elem` aItems)
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
                               (flip evalStateT s actionCancel)
                
                io $ onClicked (castToButton okButton) 
                               (flip evalStateT s actionOk)
                
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
                        listStoreGetValue ls i

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
                     atBox <- makeExerConfCheckItem  "Axiomas Disponibles" 
                                                    (map fst axiomGroup)
                                                    (map fst aTheories)
                     vBoxAdd vBox atBox
                     
                     box <- io makeOkCancelButtons
                     io $ boxPackEnd vBox box PackNatural 2
                     
                     w <- makeWindowPop vBox 300 True
                     
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
                         sep <- io hSeparatorNew
                         io $ boxPackStart vBox sep PackNatural 2

-- Crea un entry para ingresar el texto relacionado a un titulo del enunciado.
makeExerciseTitleEntry :: IState HBox
makeExerciseTitleEntry = do
                    box <- io $ hBoxNew False 0
                    
                    optionLabel <- io $ labelNew $ Just "Titulo"
                    
                    stat <- getExerciseStatement
                    entry <- io entryNew
                    io $ entrySetText entry $ (unpack . title) stat
                    
                    io $ boxPackStart box optionLabel PackNatural 10
                    io $ set optionLabel [ widgetWidthRequest := 240 ]
                    io $ boxPackStart box entry PackNatural 10
                    io $ set entry [ widgetWidthRequest := 400 ]
                    return box

-- Crea un textview para ingresar texto relacionado con los hint's del
-- enunciado.
makeExerciseTextView :: String -> (Statement -> Text) -> IState HBox
makeExerciseTextView s field = do
                    box <- io $ hBoxNew False 0
                    
                    optionLabel <- io $ labelNew $ Just s
                    
                    stat <- getExerciseStatement
                    
                    textView <- io textViewNew
                    io $ textViewSetWrapMode textView WrapWord
                    io $ set textView [ widgetWidthRequest := 400
                                      , widgetHeightRequest := 100
                                      ]
                    
                    textBuffer <- io $ textViewGetBuffer textView
                    
                    io $ textBufferSetText textBuffer (unpack $ field stat)
                    
                    io $ boxPackStart box optionLabel PackNatural 10
                    io $ set optionLabel [ widgetWidthRequest := 240 ]
                    io $ boxPackStart box textView PackNatural 10
                    
                    return box

-- Acci´on del boton Aceptar para la ventana de edici´on del enunciado.
actionOkButtonStatement :: HBox -> HBox -> HBox -> Window -> IState ()
actionOkButtonStatement titleBox statBox hintBox w = do
                     
                     updateExerciseStatementTitle titleBox
                     
                     updateExerciseStatementStat statBox
                     
                     updateExerciseStatementHints hintBox
                     
                     io (widgetDestroy w)

-- Update del titulo de un enunciado.
updateExerciseStatementTitle :: HBox -> IState ()
updateExerciseStatementTitle titleBox = do
                            [_,entry] <- io $ containerGetChildren titleBox
                            text <- io $ entryGetText (castToEntry entry)
                            stat <- getExerciseStatement
                            updateExerciseStatement (stat {title = pack text})

-- Update del cuerpo de un enunciado.
updateExerciseStatementStat :: HBox -> IState ()
updateExerciseStatementStat statBox = do
            text <- io $ getTextFromTextView statBox
            stat <- getExerciseStatement
            updateExerciseStatement (stat {stat = pack text})

-- Update del hint de un enunciado.
updateExerciseStatementHints :: HBox -> IState ()
updateExerciseStatementHints hintBox = do
            text <- io $ getTextFromTextView hintBox
            stat <- getExerciseStatement
            updateExerciseStatement (stat {hints = pack text})

-- Retorna el texto de un textView.
getTextFromTextView  :: HBox -> IO String
getTextFromTextView box = do
        [_,textView] <- containerGetChildren box
        textBuffer <- textViewGetBuffer (castToTextView textView)
        textIterStart <- textBufferGetStartIter textBuffer
        textIterEnd <- textBufferGetEndIter textBuffer
        
        textBufferGetText textBuffer textIterStart textIterEnd False

makeExerciseTitleView :: IState HBox
makeExerciseTitleView = do
            stat <- getExerciseStatement
            io $ makeExerciseStatementView " Titulo: " $ (unpack . title) stat

makeExerciseStatView :: IState HBox
makeExerciseStatView = do
            state <- getExerciseStatement
            io $ makeExerciseStatementView " Enunciado: " $ (unpack . stat) state

makeExerciseHintsView :: IState HBox
makeExerciseHintsView = do
            stat <- getExerciseStatement
            io $ makeExerciseStatementView " Hints: " $ (unpack . hints) stat

makeExerciseStatementView :: String -> String -> IO HBox
makeExerciseStatementView l info = do
                        box <- hBoxNew False 0
                        
                        label <- labelNew $ Just l
                        infoLabel <- labelNew $ Just info
                        
                        boxPackStart box label PackNatural 0
                        boxPackStart box infoLabel PackNatural 0
                        
                        return box   

makeStatementWindow :: IState ()
makeStatementWindow = do
                    vBox <- newVBox

                    titleBox <- makeExerciseTitleView
                    vBoxAdd vBox titleBox

                    statBox <- makeExerciseStatView
                    vBoxAdd vBox statBox

                    hintBox <- makeExerciseHintsView
                    vBoxAdd vBox hintBox

                    closeButton <- io $ buttonNewWithLabel "Close"
                    io $ boxPackEnd vBox closeButton PackNatural 2

                    w <- makeWindowPop vBox 400 True
                    io $ onClicked (castToButton closeButton) (widgetDestroy w)
                    return ()
    where
        vBoxAdd :: WidgetClass w => VBox -> w -> IState ()
        vBoxAdd vBox w = do
                         io $ boxPackStart vBox w PackNatural 2
                         sep <- io hSeparatorNew
                         io $ boxPackStart vBox sep PackNatural 2

-- Crea una ventana que permite editar los campos de un enunciado.
makeStatementEditWindow :: IState ()
makeStatementEditWindow =  do
                    vBox <- newVBox

                    titleBox <- makeExerciseTitleEntry
                    vBoxAdd vBox titleBox

                    statBox <- makeExerciseTextView "Enunciado" stat
                    vBoxAdd vBox statBox

                    hintBox <- makeExerciseTextView "Hint's" hints
                    vBoxAdd vBox hintBox

                    box <- io makeOkCancelButtons
                    io $ boxPackEnd vBox box PackNatural 2

                    w <- makeWindowPop vBox 400 True

                    setupOkCancelButtons box 
                        (actionOkButtonStatement titleBox statBox hintBox w)
                        (io $ widgetDestroy w)
    where
        vBoxAdd :: WidgetClass w => VBox -> w -> IState ()
        vBoxAdd vBox w = do
                         io $ boxPackStart vBox w PackNatural 2
                         sep <- io hSeparatorNew
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

exerciseFileFilter :: (FileChooserClass f, MonadIO m) => f -> m ()
exerciseFileFilter dialog = io $ setFileFilter dialog "*.exer" "Ejercicio de equ"

-- Guarda un ejercicio.
saveExercise :: IState ()
saveExercise = getExercise >>= \mexer ->
               case mexer of
                   Nothing -> makeErrWindow "Ningun ejercicio para guardar."
                   Just _ -> setupExerciseToSave >>= \exer -> 
                             getExerciseStatement >>= \stat ->
                             saveDialog "Guardar ejercicio"
                                        (configFileName stat)
                                        exerciseFileFilter
                                        exer >> return ()
    where
        configFileName :: Statement -> String
        configFileName stat = map (\c -> if c == ' ' then '_' else c) 
                                  (unpack $ title stat) ++ ".exer"
        takeProof :: Maybe ProofState -> Proof
        takeProof = toProof . fromJust . goTop . pFocus . proof . fromJust
        takeAnnots :: Maybe ProofState -> ProofAnnotation
        takeAnnots = toProof . fromJust . goTop . pFocus . proofAnnots . fromJust
        setupExerciseToSave :: IState Exercise
        setupExerciseToSave = do
                    mps <- getProofState 
                    when (isJust mps) (updateExerciseProof (takeProof mps) >>
                                       updateExerciseAnnots (takeAnnots mps))
                    Just initE <- getInitialExpr
                    stat <- getExerciseStatement
                    updateExerciseStatement (stat {initExpr = initE})
                    Just exer <- getExercise
                    return exer

-- Cargar el ejercicio al estado.
loadExercise :: IState Bool
loadExercise = do
            s <- get
            io $ dialogLoad
                "Cargar ejercicio"
                exerciseFileFilter
                (flip evalStateT s . updateExercise)

-- Configura la prueba a mostrar cuando cargamos un ejercicio para editar.
setupProofFromExercise :: VBox -> VBox -> ExprWidget -> IState ()
setupProofFromExercise centralBox truthBox initExprWidget = do
            discardProof centralBox initExprWidget
            e <- getExerciseStatementInitExpr 
            initExprState $ toFocus $ getPreExpr e
            mproof <- getExerciseProof
            tl <- getAxiomCtrl
            theories <- getExerciseConfATheories
            ts <- changeTruthList  (theoriesInGroup theories) tl
            eventsTruthList tl ts
            when (isJust mproof)
                 (createNewProof mproof centralBox truthBox initExprWidget) 
            mAnnots <- getExerciseAnnots
            when (isJust mAnnots)
                 (updateProofAnnots . fromJust . createListedProof . toProofFocus . fromJust $ mAnnots)


-- Crea un ejercicio.
makeExercise :: IState ()
makeExercise = getInitialExpr >>= updateExercise . initExercise . fromJust
    where
        initExercise :: Expr -> Exercise
        initExercise = flip createExercise Nothing
