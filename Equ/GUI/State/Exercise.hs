module Equ.GUI.State.Exercise where

import Equ.Exercise
import Equ.Exercise.Conf
import Equ.Theories (Grouped (..))
import Equ.Proof.Proof(Axiom (..))

import Equ.GUI.State
import Equ.GUI.Types

import Data.Maybe
import qualified Data.Set as S (Set)

-- Retorna el tipo de prueba relacionado a la configuraci´on del ejercicio.
getExerciseConfTypeProof :: IState (TypeProof)
getExerciseConfTypeProof = getExerciseConf >>= return . eConfTypeProof

-- Retorna el modo de re-escritura relacionado a la configuraci´on 
-- del ejercicio.
getExerciseConfRewriteMode :: IState (RewriteMode)
getExerciseConfRewriteMode = getExerciseConf >>= return . eConfRewriteMode

-- Retorna el tipo de checkeo de tipos relacionado a la configuraci´on 
-- del ejercicio.
getExerciseConfTypeCheck :: IState (TypeCheck)
getExerciseConfTypeCheck = getExerciseConf >>= return . eConfTypeCheck

-- Retorna la informacion a la informaci´on a mostrar relacionado a la 
-- configuraci´on del ejercicio.
getExerciseConfExplicitInfo :: IState (S.Set Explicit)
getExerciseConfExplicitInfo = getExerciseConf >>= return . eConfExplicit

-- Retorna la lista de teorias disponibles relacionado a la 
-- configuraci´on del ejercicio.
getExerciseConfATheories :: IState (Grouped Axiom)
getExerciseConfATheories = getExerciseConf >>= return . eConfAvaibleTheories

-- Retorna la configuraci´on del ejercicio.
getExerciseConf :: IState (ExerciseConf)
getExerciseConf = getExercise >>= return . exerConf . fromJust

-- Retorna el enunciado del ejercicio.
getExerciseStatement :: IState Statement
getExerciseStatement = getExercise >>= return . exerStatement . fromJust 

-- Retorna el ejercicio.
getExercise :: IState (Maybe Exercise)
getExercise = getStatePart gExercise

-- Update de la configuraci´on del ejercicio.
updateExerciseConf :: ExerciseConf -> IState ()
updateExerciseConf exerConf = do
                              Just exer <- getExercise 
                              updateExercise $ exer {exerConf = exerConf}
                              
-- Update del enunciado de ejercicio.
updateExerciseStatement :: Statement -> IState ()
updateExerciseStatement exerStat = do
                              Just exer <- getExercise 
                              updateExercise $ exer {exerStatement = exerStat}

-- Update del ejercicio.
updateExercise :: Exercise -> IState ()
updateExercise exer = update (updateExercise' exer)
    where
        updateExercise' :: Exercise -> GState -> GState
        updateExercise' exer gs = gs {gExercise = Just exer}
