module Equ.GUI.Exercise where

import Graphics.UI.Gtk hiding (get)

import Equ.Exercise
import Equ.Exercise.Conf

import Equ.GUI.Types
import Equ.GUI.Utils
import Equ.GUI.State
import Equ.GUI.State.Exercise 
import Equ.GUI.Widget
import Equ.Theories (relationList, axiomGroup, Grouped (..))
import Equ.Proof.Proof(Axiom (..))
import Equ.Proof (toProof)
import Equ.Rule hiding (rel)

import Data.Maybe (fromJust)
import Data.Text (unpack, pack)
import Data.List (elemIndex, find)
import qualified Data.Set as S
import qualified Data.Foldable as F

import Control.Monad.State.Strict (when, get, evalStateT)

setupExerciseToolbar :: HBox -> IState ()
setupExerciseToolbar b = do
            (exerConfButton, statementButton, associateProofButton) <- io $ makeToolButtons
            s <- get
            io $ onToolButtonClicked exerConfButton 
                                    (evalStateT makeExerConfWindow s)
            io $ onToolButtonClicked statementButton 
                                    (evalStateT makeStatementWindow s)
            io $ onToolButtonClicked associateProofButton
                                    (evalStateT makeAssocProofWindow s)
            return ()
    where
        makeToolButtons :: IO (ToolButton, ToolButton, ToolButton)
        makeToolButtons = do
            sep <- separatorToolItemNew
            exerConfButton <- toolButtonNewFromStock stockProperties
            statementButton <- toolButtonNewFromStock stockSelectAll
            associateProofButton <- toolButtonNewFromStock stockRevertToSaved
            
            boxPackStart b sep PackNatural 0
            boxPackStart b exerConfButton PackNatural 0
            boxPackStart b statementButton PackNatural 0
            boxPackStart b associateProofButton PackNatural 0
            
            widgetSetNoShowAll b True 
            return (exerConfButton, statementButton, associateProofButton)

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

makeOkCancelButtons :: IO HBox
makeOkCancelButtons = do
                      box <- hBoxNew False 0
                      
                      okButton <- buttonNewWithLabel "Aceptar"
                      cancelButton <- buttonNewWithLabel "Cancelar"
                      
                      boxPackEnd box cancelButton PackNatural 2
                      boxPackEnd box okButton PackNatural 2
                      
                      return box

setupOkCancelButtons :: HBox -> IState () -> IState () -> IState ()
setupOkCancelButtons b actionOk actionCancel = do
                [okButton, cancelButton] <- io $ containerGetChildren b
                
                s <- get 
                
                io $ onClicked (castToButton cancelButton) 
                               (flip evalStateT s $ actionCancel)
                
                io $ onClicked (castToButton okButton) 
                               (flip evalStateT s $ actionOk)
                
                return ()

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

getActiveItemFromCombo :: Show a => (HBox, ListStore a) -> IO a
getActiveItemFromCombo (b, ls) = do
                        [_, cBox] <- containerGetChildren b
                        i <- comboBoxGetActive (castToComboBox cBox)
                        item <- listStoreGetValue ls i
                        return item

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
                     
                     w <- io $ windowNew
                     io $ containerAdd w vBox
                     io $ set w [windowDefaultWidth := 300]
                     io $ windowSetPosition w WinPosCenterAlways
                     io $ widgetShowAll w
                     
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

makeExerciseGoal :: IState HBox
makeExerciseGoal = do
                hbox <- io $ hBoxNew False 0
                    
                optionLabel <- io $ labelNew $ Just "Meta (?)"
                
                vbox <- io $ vBoxNew False 0
                
                stat <- getExerciseStatement
                
                initEntry <- io $ entryNew
                io $ entrySetText initEntry $ (show . initExpr . goal) stat
                
                
                ls <- io $ listStoreNew relationList 
                cbox <- io $ comboBoxNewWithModel ls
                cellRenderer <- io $ cellRendererTextNew
                io $ cellLayoutPackStart cbox cellRenderer True
                io $ cellLayoutSetAttributes cbox cellRenderer ls 
                                        (\s -> [cellText := unpack $ relRepr s])
                
                l <- io $ listStoreToList ls
                item <- return $ (rel . goal) stat
                io $ comboBoxSetActive cbox (fromJust $ elemIndex item l)
                
                finalEntry <- io $ entryNew
                io $ entrySetText finalEntry $ (show . finalExpr . goal) stat
                
                io $ boxPackStart vbox initEntry PackNatural 2
                io $ boxPackStart vbox cbox PackNatural 2
                io $ boxPackStart vbox finalEntry PackNatural 2
                
                io $ boxPackStart hbox optionLabel PackGrow 0
                io $ boxPackStart hbox vbox PackNatural 0
                
                return hbox

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

actionOkButtonStatement :: HBox -> HBox -> HBox -> Window -> IState ()
actionOkButtonStatement titleBox goalBox hintBox w = do
                     
                     updateExerciseStatementTitle titleBox
                     
                     updateExerciseStatementGoal goalBox
                     
                     updateExerciseStatementHint hintBox
                     
                     io (widgetDestroy w)

updateExerciseStatementTitle :: HBox -> IState ()
updateExerciseStatementTitle titleBox = do
                     [_,entry] <- io $ containerGetChildren titleBox
                     text <- io $ entryGetText (castToEntry entry)
                     stat <- getExerciseStatement
                     updateExerciseStatement (stat {title = pack text})

updateExerciseStatementGoal :: HBox -> IState ()
updateExerciseStatementGoal goalBox = return ()

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

makeStatementWindow :: IState ()
makeStatementWindow =  do
                     vBox <- newVBox
                     
                     titleBox <- makeExerciseTitleEntry
                     vBoxAdd vBox titleBox
                     
                     goalBox <- makeExerciseGoal
                     vBoxAdd vBox goalBox
                     
                     hintBox <- makeExerciseHintEntry
                     vBoxAdd vBox hintBox
                     
                     box <- io $ makeOkCancelButtons
                     io $ boxPackEnd vBox box PackNatural 2
                     
                     w <- io $ windowNew
                     io $ containerAdd w vBox
                     io $ set w [windowDefaultWidth := 400]
                     io $ windowSetPosition w WinPosCenterAlways
                     io $ widgetShowAll w
                     
                     setupOkCancelButtons box 
                        (actionOkButtonStatement titleBox goalBox hintBox w)
                        (io $ widgetDestroy w)
    where
        vBoxAdd :: WidgetClass w => VBox -> w -> IState ()
        vBoxAdd vBox w = do
                         io $ boxPackStart vBox w PackNatural 2
                         sep <- io $ hSeparatorNew
                         io $ boxPackStart vBox sep PackNatural 2

makeAssocProofWindow :: IState ()
makeAssocProofWindow = do
            proofState <- getProofState
            case proofState of
                Nothing -> makeErrWindow 
                           "No existe prueba para asociar al ejercicio. "
                Just ps -> getExercise >>= \(Just exer) ->
                           updateExercise $ 
                                exer {exerProof = Just $ toProof $ proof ps }

saveExercise :: IState ()
saveExercise = return ()

makeExercise :: IState ()
makeExercise = updateExercise initExercise
    where
        initExercise :: Exercise
        initExercise = createExercise
