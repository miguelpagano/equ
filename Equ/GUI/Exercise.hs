module Equ.GUI.Exercise where

import Graphics.UI.Gtk hiding (get)

import Equ.Exercise
import Equ.Exercise.Conf

import Equ.GUI.Types
import Equ.GUI.Utils
import Equ.GUI.State.Exercise 
import Equ.GUI.Widget

import Data.Maybe (fromJust)
import Data.List (elemIndex, find)
import qualified Data.Set as S

import Control.Monad.State.Strict (when, get, evalStateT)

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


makeExerConfCheckItem :: String -> [Explicit] -> IState HBox
makeExerConfCheckItem s items = do
                                box <- io $ hBoxNew False 0
                                optionLabel <- io $ labelNew $ Just s
                                
                                itemBox <- io $ vBoxNew False 0
                                makeExerConfCheckItem' items itemBox
                                
                                io $ boxPackStart box optionLabel PackGrow 0
                                io $ boxPackStart box itemBox PackNatural 0
                                
                                return box

makeExerConfCheckItem' :: BoxClass b => [Explicit] -> b -> IState b
makeExerConfCheckItem' [] b =  return b
makeExerConfCheckItem' (item:items) b = do
                     cbutton <- io $ checkButtonNewWithLabel $ show item
                     io $ boxPackStart b cbutton PackNatural 0
                     exerConf <- getExerciseConf
                     when (S.member item $ eConfExplicit exerConf) 
                          (io $ set cbutton [toggleButtonActive := True])
                     
                     makeExerConfCheckItem' items b

makeOkCancelButtons :: IO HBox
makeOkCancelButtons = do
                      box <- hBoxNew False 0
                      
                      okButton <- buttonNewWithLabel "Aceptar"
                      cancelButton <- buttonNewWithLabel "Cancelar"
                      
                      boxPackEnd box cancelButton PackNatural 2
                      boxPackEnd box okButton PackNatural 2
                      
                      return box

setupOkCancelButtons :: HBox -> (HBox, ListStore TypeProof) -> 
                                (HBox, ListStore RewriteMode) -> 
                                (HBox, ListStore TypeCheck) -> 
                                HBox -> [Explicit] -> Window -> IState ()
setupOkCancelButtons b tpBox rwBox tcBox infoBox infoList w = do
                [okButton, cancelButton] <- io $ containerGetChildren b
                
                io $ onClicked (castToButton cancelButton) (widgetDestroy w)
                
                s <- get 
                io $ onClicked (castToButton okButton) 
                    (flip evalStateT s $
                    io (getActiveItemFromCombo tpBox) >>= \item ->
                    getExerciseConf >>= \exerConf ->
                    updateExerciseConf (exerConf {eConfTypeProof = item}) >>
                    
                    io (getActiveItemFromCombo rwBox) >>= \item ->
                    getExerciseConf >>= \exerConf ->
                    updateExerciseConf (exerConf {eConfRewriteMode = item}) >>
                    
                    io (getActiveItemFromCombo tcBox) >>= \item ->
                    getExerciseConf >>= \exerConf ->
                    updateExerciseConf (exerConf {eConfTypeCheck = item}) >>
                    
                    getActiveItemsFromCheck infoBox infoList >>= \set ->
                    getExerciseConf >>= \exerConf ->
                    updateExerciseConf (exerConf {eConfExplicit = set}) >>
                    io (widgetDestroy w))
                
                return ()

getActiveItemsFromCheck :: HBox -> [Explicit] -> IState (S.Set Explicit)
getActiveItemsFromCheck b infoList = do
                            [_, itemBox] <- io $ containerGetChildren b
                            itemList <- io $ containerGetChildren (castToBox itemBox)
                            getActiveItemsFromCheck' itemList infoList S.empty
                            
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
                     
                     infoBox <- makeExerConfCheckItem 
                                                    ("Información a mostrar" 
                                                    ++ "\n" 
                                                    ++ "sobre el objetivo" )
                                                    explicitOptionList
                     vBoxAdd vBox infoBox
                     
                     box <- io $ makeOkCancelButtons
                     io $ boxPackEnd vBox box PackNatural 2
                     
                     w <- io $ windowNew
                     io $ containerAdd w vBox
                     io $ set w [windowDefaultWidth := 300]
                     io $ windowSetPosition w WinPosCenterAlways
                     io $ widgetShowAll w
                     
                     setupOkCancelButtons box (tpBox, tpLs) (rwBox, rwLs) 
                                              (tcBox, tcLs) infoBox explicitOptionList w
    where
        vBoxAdd :: WidgetClass w => VBox -> w -> IState ()
        vBoxAdd vBox w = do
                         io $ boxPackStart vBox w PackNatural 2
                         sep <- io $ hSeparatorNew
                         io $ boxPackStart vBox sep PackNatural 2

makeStatementWindow :: IState ()
makeStatementWindow = return ()

saveExercise :: IState ()
saveExercise = return ()

makeExercise :: IState ()
makeExercise = updateExercise initExercise
    where
        initExercise :: Exercise
        initExercise = createExercise
