-- | Este m&#243;dulo define la noci&#243;n de un ejercicio en equ.
module Equ.Exercise where

import Equ.Exercise.Conf

import Equ.Expr
import qualified Equ.Rule as R
import Equ.Proof

import Data.Text hiding (null)
import qualified Data.Map as M 

-- Anotacin para una expresi´on.
type Annot = (Text, ProofFocus)

-- Conjunto de anotaciones para una prueba.
type Annotations = [Annot]

-- Objetivo del ejercicio.
data Goal = Goal { initExpr :: Maybe Expr
                 , rel :: R.Relation
                 , finalExpr :: Maybe Expr
                 }

-- Enunciado del ejercicio.
data Statement = Statement { title :: Text
                           , goal :: Goal
                           , hints :: Text
                           }

-- Representacion del ejercicio en equ.
data Exercise = Exercise { exerConf :: ExerciseConf
                         , exerStatement :: Statement
                         , exerProof :: Proof
                         , exerAnnots :: Annotations
                         }

-- Crea un ejercicio a partir de una configuraci´on y un enunciado.
-- En el cual la prueba es un hueco con el contexto y relaci´on propio de la
-- configuraci´on del ejercicio.
createEmptyExercise :: ExerciseConf -> Statement -> Exercise
createEmptyExercise exerConf stmnt = Exercise exerConf stmnt p []
    where
        ctx :: Maybe Ctx
        ctx = let c = eConfInitCtx exerConf
              in case M.null $ c of
                    True -> Nothing
                    False -> Just $ c
        r :: R.Relation
        r = rel $ goal stmnt
        p :: Proof
        p = holeProof ctx r
