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

-- Enunciado del ejercicio.
data Statement = Statement { title :: Text
                           , initExpr :: Expr
                           , hints :: Text
                           } deriving Show

-- Representacion del ejercicio en equ.
data Exercise = Exercise { exerConf :: ExerciseConf
                         , exerStatement :: Statement
                         , exerProof :: Maybe Proof
                         , exerAnnots :: Annotations
                         }

instance Show Exercise where
    show exer = show (exerConf exer) ++ " " ++
                show (exerStatement exer) ++ " " ++
                show (exerProof exer)

createStatement :: Expr -> Statement
createStatement e = Statement empty e empty

-- Crea un ejercicio a partir de una configuraci´on y un enunciado.
-- En el cual la prueba es un hueco con el contexto y relaci´on propio de la
-- configuraci´on del ejercicio.
createExercise :: Expr -> Exercise
createExercise e = Exercise exerConf stmnt Nothing []
    where
        exerConf :: ExerciseConf
        exerConf = createExerciseConf
        stmnt :: Statement
        stmnt = createStatement e
