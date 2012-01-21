module Equ.GUI.Truth where

import Equ.PreExpr
import Equ.GUI.Types
import Equ.GUI.State
import Equ.GUI.Utils
import Equ.GUI.TruthList
import Equ.TypeChecker
import Equ.Theories

import qualified Graphics.UI.Gtk as G
import Graphics.UI.Gtk hiding (eventButton, eventSent,get)
import Data.Text (pack)
import qualified Data.Foldable as F (mapM_)
import Data.Maybe (fromJust)

addTheoremUI :: TreeStore (String, HBox -> IRG) -> String -> IState ()
addTheoremUI tl th_name = getValidProof >>= return . fromRight >>= \proof ->
                          addTheorem (createTheorem (pack th_name) proof) >>=
                          io . addTheoList tl

addHypothesisUI :: TreeStore (String, HBox -> IRG) -> IState ()
addHypothesisUI tl = getExpr >>=
                     addGlobalHypothesis . toExpr >>= \n ->
                     flip F.mapM_ n $ \x -> getGlobalHypothesis x >>= 
                                           F.mapM_ (io . addHypoList tl)