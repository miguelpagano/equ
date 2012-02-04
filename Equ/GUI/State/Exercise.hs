module Equ.GUI.State.Exercise where

import Equ.Exercise
import Equ.Exercise.Conf

import Equ.GUI.State
import Equ.GUI.Types

import Data.Maybe

getExerciseConfTypeProof :: IState (TypeProof)
getExerciseConfTypeProof = getExerciseConf >>= return . eConfTypeProof

getExerciseConfRewriteMode :: IState (RewriteMode)
getExerciseConfRewriteMode = getExerciseConf >>= return . eConfRewriteMode

getExerciseConfTypeCheck :: IState (TypeCheck)
getExerciseConfTypeCheck = getExerciseConf >>= return . eConfTypeCheck

getExerciseConf :: IState (ExerciseConf)
getExerciseConf = getExercise >>= return . exerConf . fromJust

getExercise :: IState (Maybe Exercise)
getExercise = getStatePart gExercise

updateExerciseConf :: ExerciseConf -> IState ()
updateExerciseConf exerConf = do
                              Just exer <- getExercise 
                              updateExercise $ exer {exerConf = exerConf}

updateExercise :: Exercise -> IState ()
updateExercise exer = update (updateExercise' exer)

updateExercise' :: Exercise -> GState -> GState
updateExercise' exer gs = gs {gExercise = Just exer}
