module Equ.Exercise.Conf where

import Equ.Theories (Grouped (..))
import Equ.Proof.Proof(Axiom (..))
import Equ.Proof hiding (Simple, Focus, Cases)

import Data.Text hiding (empty, map)
import qualified Data.Set as S (Set (..), empty)

import Control.Applicative ((<$>), (<*>))
import Data.Serialize (Serialize, get, getWord8, put, putWord8)

{- Auto: se hace automáticamente al parsear
   Manual: no se infiere nada, se hace a mano.
   Infer: se puede usar el botón “Inferir” en la caja del árbol.
-}
data TypeCheck = Auto 
               | Manual 
               | Infer
    deriving (Show, Eq)

instance Serialize TypeCheck where
    put Auto = putWord8 0
    put Manual = putWord8 1
    put Infer = putWord8 2
    
    get = do
    tag_ <- getWord8
    case tag_ of
        0 -> return Auto
        1 -> return Manual
        2 -> return Infer
        _ -> fail $ "SerializeErr TypeCheck " ++ show tag_

-- Tipo de re-escritura.
data RewriteMode = Simple -- ^ Directa.
                 | List     -- ^ Se puede ver la lista de resultados.
                 | Focus -- ^ Se debe decir dónde se debe aplicar la regla.
    deriving (Show, Eq)

instance Serialize RewriteMode where
    put Simple = putWord8 0
    put List = putWord8 1
    put Focus = putWord8 2
    
    get = do
    tag_ <- getWord8
    case tag_ of
        0 -> return Simple
        1 -> return List
        2 -> return Focus
        _ -> fail $ "SerializeErr RewriteMode " ++ show tag_

-- Tipo de prueba.
data TypeProof = Direct -- ^ Prueba directa.
               | Cases  -- ^ Prueba por casos.
               | Induction -- ^ Prueba por inducción.
               | Deduction -- ^ Usando metateorema de la deducción.
    deriving (Show, Eq)

instance Serialize TypeProof where
    put Direct = putWord8 0
    put Cases = putWord8 1
    put Induction = putWord8 2
    put Deduction = putWord8 3
    
    get = do
    tag_ <- getWord8
    case tag_ of
        0 -> return Direct
        1 -> return Cases
        2 -> return Induction
        3 -> return Deduction
        _ -> fail $ "SerializeErr TypeProof " ++ show tag_

data Explicit = Initial 
              | Relation 
              | Final
    deriving (Show, Eq, Ord)

instance Serialize Explicit where
    put Initial = putWord8 0
    put Relation = putWord8 1
    put Final = putWord8 2
    
    get = do
    tag_ <- getWord8
    case tag_ of
        0 -> return Initial
        1 -> return Relation
        2 -> return Final
        _ -> fail $ "SerializeErr Explicit " ++ show tag_

-- Conjunto de informacion a mostar relacionada con el objetivo del ejercicio.
type ExplicitInfo = S.Set Explicit

-- Configuracion de un ejercicio.
data ExerciseConf = ExerciseConf { eConfTypeProof :: TypeProof
                                 , eConfExplicit :: ExplicitInfo
                                 , eConfRewriteMode :: RewriteMode
                                 , eConfTypeCheck :: TypeCheck
                                 , eConfAvaibleTheories :: Grouped Axiom
                                 }

instance Show ExerciseConf where
    show exerConf = show (eConfTypeProof exerConf) ++ " " ++ 
                    show (eConfRewriteMode exerConf) ++ " " ++
                    show (eConfTypeCheck exerConf) ++ " " ++
                    show (eConfExplicit exerConf)  ++ " " ++
                    show (map (fst) $ eConfAvaibleTheories exerConf)

instance Serialize ExerciseConf where
    put (ExerciseConf tp ei rw tc ga) = put tp >> put ei >> put rw >>
                                        put tc >> put ga

    get = ExerciseConf <$> get <*> get <*> get <*> get <*> get

createExerciseConf :: ExerciseConf
createExerciseConf = ExerciseConf Direct S.empty Simple Auto []

typeCheckOptionList :: [TypeCheck]
typeCheckOptionList = [Auto, Manual, Infer]

rewriteModeOptionList :: [RewriteMode]
rewriteModeOptionList = [Simple, List, Focus]

typeProofOptionList :: [TypeProof]
typeProofOptionList = [Direct, Cases, Induction, Deduction]

explicitOptionList :: [Explicit]
explicitOptionList = [Initial, Relation, Final]
