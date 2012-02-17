{-# Language TypeSynonymInstances #-}
   -- | Este m&#243;dulo define la noci&#243;n de un ejercicio en equ.
module Equ.Exercise where

import Equ.Exercise.Conf (ExerciseConf, createExerciseConf)

import Equ.Expr
import qualified Equ.Rule as R
import Equ.Proof

import Data.Text hiding (null)
import qualified Data.Map as M 

import Control.Applicative ((<$>), (<*>))
import Data.Serialize (Serialize, get, getWord8, put, putWord8)

-- Anotacin para una expresi´on.
type Annotation = Text

-- Conjunto de anotaciones para una prueba.
type ProofAnnotation = Proof' () () () Annotation

type ProofFocusAnnots = ProofFocus' () () () Annotation

instance Show ProofAnnotation where
    show (Hole _ _ a a') = "Hole " ++ show a ++ " " ++ show a'
    show (Simple _ _ a a' _) = "Simple " ++ show a ++ " " ++ show a'
    show (Trans _ _ a a' a'' p p') = "Trans " ++ show a ++ " " ++ show a' ++ " " ++
                                     show a'' ++ " " ++ show p ++ " " ++ show p'
    show _ = ""

instance Serialize ProofAnnotation where
    put Reflex = putWord8 0
    put (Hole _ _ annot annot') = putWord8 1 >> put annot >> put annot'
    put (Simple _ _ annot annot' _) = putWord8 2 >> put annot >> put annot'
    put (Trans _ _ annot annot' annot'' p p') = 
                putWord8 3 >> put annot >> put annot' >> put annot'' >>
                put p >> put p'
    put (Cases _ _ annot annot' annot'' lfp) = 
                putWord8 4 >> put annot >> put annot' >> put annot''  >>
                put lfp
    put (Ind _ _ annot annot' lf llfp) = 
                putWord8 5 >> put annot >> put annot' >>
                put lf >> put llfp
    put (Deduc _ annot annot' p) = 
                putWord8 6 >> put annot >> put annot' >> put p
    put (Focus _ _ annot annot' p) = 
                putWord8 7 >> put annot >> put annot' >> put p
    
    get = getWord8 >>= \tag_ ->
        case tag_ of
        0 -> return Reflex 
        1 -> Hole () () <$> get <*> get
        2 -> Simple () () <$> get <*> get <*> return ()
        3 -> Trans () () <$> get <*> get <*> get <*> get <*> get
        4 -> Cases () () <$> get <*> get <*> get <*> get
        5 -> Ind () () <$> get <*> get <*> get <*> get
        6 -> Deduc () <$> get <*> get <*> get
        7 -> Focus () () <$> get <*> get <*> get
        _ -> fail $ "SerializeErr ProofAnnotation " ++ show tag_

-- Enunciado del ejercicio.
data Statement = Statement { title :: Text
                           , stat :: Text
                           , initExpr :: Expr
                           , hints :: Text
                           } deriving Show

instance Serialize Statement where
    put (Statement title stat initExpr hints) = 
        put title >> put stat >> put initExpr >> put hints
    
    get = Statement <$> get <*> get <*> get <*> get

-- Representacion del ejercicio en equ.
data Exercise = Exercise { exerConf :: ExerciseConf
                         , exerStatement :: Statement
                         , exerProof :: Maybe Proof
                         , exerAnnots :: Maybe ProofAnnotation
                         }

instance Serialize Exercise where
    put (Exercise exerConf exerStat exerProof exerAnnots) =
        put exerConf >> put exerStat >> put exerProof >> put exerAnnots
        
    get = Exercise <$> get <*> get <*> get <*> get

instance Show Exercise where
    show exer = show (exerConf exer) ++ " " ++
                show (exerStatement exer) ++ " " ++
                show (exerProof exer)

emptyProofAnnots :: ProofFocusAnnots
emptyProofAnnots = toProofFocus $ Hole () () empty empty

addEmptyStepAnnots :: ProofFocusAnnots -> ProofFocusAnnots
addEmptyStepAnnots (p@(Hole _ _ a a'),path) = 
    (Trans () () a empty a' (Hole () () a empty) (Hole () () empty a'),path)
-- Si le pasamos una prueba simple, la considera un hueco
addEmptyStepAnnots (p@(Simple _ _ a a' _),path) = 
    (Trans () () a empty a' (Hole () () a empty) (Hole () () empty a'),path)
addEmptyStepAnnots p = p

createStatement :: Expr -> Statement
createStatement e = Statement empty empty e empty

-- Crea un ejercicio a partir de una configuraci´on y un enunciado.
-- En el cual la prueba es un hueco con el contexto y relaci´on propio de la
-- configuraci´on del ejercicio.
createExercise :: Expr -> Maybe ProofAnnotation -> Exercise
createExercise e mpa = Exercise exerConf stmnt Nothing mpa
    where
        exerConf :: ExerciseConf
        exerConf = createExerciseConf
        stmnt :: Statement
        stmnt = createStatement e
