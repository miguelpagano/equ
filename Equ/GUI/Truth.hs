module Equ.GUI.Truth where


import Equ.GUI.Types
import Equ.GUI.State
import Equ.GUI.Utils
import Equ.GUI.TruthList
import Equ.GUI.Widget

import Equ.PreExpr
import Equ.TypeChecker
import Equ.Theories

import qualified Graphics.UI.Gtk as G
import Graphics.UI.Gtk hiding (eventButton, eventSent,get)
import Data.Text (pack)
import qualified Data.Foldable as F (mapM_)
import Data.Maybe (fromJust)

import Control.Monad.State (evalStateT,get)
import Control.Monad(liftM, when)
import Control.Monad.Trans(liftIO)


addTheoremUI :: TreeStore (String, HBox -> IRG) -> String -> IState ()
addTheoremUI tl th_name = getValidProof >>= return . fromRight >>= \proof ->
                          addTheorem (createTheorem (pack th_name) proof) >>=
                          io . addTheoList tl

addHypothesisUI :: TreeStore (String, HBox -> IRG) -> IState ()
addHypothesisUI tl = getExpr >>=
                     addGlobalHypothesis . toExpr >>= \n ->
                     flip F.mapM_ n $ \x -> getGlobalHypothesis x >>= 
                                           F.mapM_ (io . addHypoList tl)




saveTheorem :: GRef -> TreeStore (String, HBox -> IRG) -> IO ()
saveTheorem ref aListStore = evalStateT (updateValidProof >> checkValidProof) ref >>= \valid ->
                             debug ("valid is " ++ show valid) >>
                             if valid then saveTheoremDialog ref aListStore
                                      else errorDialog "La prueba no es válida"


-- | Dialogo para guardar una prueba como teorema de Equ. Asume que la prueba es válida.

saveTheoremDialog :: GRef -> TreeStore (String, HBox -> IRG) -> IO ()
saveTheoremDialog ref aListStore = do
    dialog <- dialogNew
    set dialog [windowTitle := "Guardar Teorema"]
    dialogAddButton dialog stockApply ResponseApply
    dialogAddButton dialog stockCancel ResponseCancel
    box <- dialogGetUpper dialog
    
    hbox1 <- hBoxNew False 2
    labelName <- labelNew $ Just "Nombre del teorema:"
    entry <- liftIO entryNew
    boxPackStart hbox1 labelName PackNatural 2
    boxPackStart hbox1 entry PackNatural 2
    
    hbox2 <- hBoxNew False 2
    labelExprTitle <- labelNew $ Just "Expresión:"
    labelExpr <- labelNew Nothing
    boxPackStart hbox2 labelExprTitle PackNatural 2
    boxPackStart hbox2 labelExpr PackNatural 2
    
    boxPackStart box hbox1 PackNatural 2
    boxPackStart box hbox2 PackNatural 2
    
    evalStateT (getExprProof >>= \expr ->
                liftIO $ labelSetText labelExpr (show expr)) ref
    
    widgetShowAll box
    
    response <- dialogRun dialog
    case response of
      ResponseApply -> entryGetText entry >>= \th_name ->
                      evalStateT (addTheoremUI aListStore th_name) ref
      _ -> return ()
    widgetDestroy dialog           
