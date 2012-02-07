module Equ.GUI.State.Exercise where

import Equ.Exercise
import Equ.Exercise.Conf
import Equ.Theories (Grouped (..))
import Equ.Proof.Proof(Axiom (..))

import Equ.GUI.State
import Equ.GUI.Types

import Data.Maybe
import qualified Data.Set as S (Set)

getExerciseConfTypeProof :: IState (TypeProof)
getExerciseConfTypeProof = getExerciseConf >>= return . eConfTypeProof

getExerciseConfRewriteMode :: IState (RewriteMode)
getExerciseConfRewriteMode = getExerciseConf >>= return . eConfRewriteMode

getExerciseConfTypeCheck :: IState (TypeCheck)
getExerciseConfTypeCheck = getExerciseConf >>= return . eConfTypeCheck

getExerciseConfExplicitInfo :: IState (S.Set Explicit)
getExerciseConfExplicitInfo = getExerciseConf >>= return . eConfExplicit

getExerciseConfATheories :: IState (Grouped Axiom)
getExerciseConfATheories = getExerciseConf >>= return . eConfAvaibleTheories

getExerciseConf :: IState (ExerciseConf)
getExerciseConf = getExercise >>= return . exerConf . fromJust

getExerciseStatement :: IState Statement
getExerciseStatement = getExercise >>= return . exerStatement . fromJust 

getExercise :: IState (Maybe Exercise)
getExercise = getStatePart gExercise

updateExerciseConf :: ExerciseConf -> IState ()
updateExerciseConf exerConf = do
                              Just exer <- getExercise 
                              updateExercise $ exer {exerConf = exerConf}
                              
updateExerciseStatement :: Statement -> IState ()
updateExerciseStatement exerStat = do
                              Just exer <- getExercise 
                              updateExercise $ exer {exerStatement = exerStat}

updateExercise :: Exercise -> IState ()
updateExercise exer = update (updateExercise' exer)

updateExercise' :: Exercise -> GState -> GState
updateExercise' exer gs = gs {gExercise = Just exer}
