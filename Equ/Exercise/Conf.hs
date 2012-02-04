module Equ.Exercise.Conf where

import Data.Text hiding (empty)
import qualified Data.Set as S (Set (..), empty)
import qualified Data.Map as M (Map (..), empty)

import Equ.Proof hiding (Simple, Focus, Cases)

{- Auto: se hace automáticamente al parsear
   Manual: no se infiere nada, se hace a mano.
   Infer: se puede usar el botón “Inferir” en la caja del árbol.
-}
data TypeCheck = Auto 
               | Manual 
               | Infer
    deriving (Show, Eq)

-- Tipo de re-escritura.
data RewriteMode = Simple -- ^ Directa.
                 | List     -- ^ Se puede ver la lista de resultados.
                 | Focus -- ^ Se debe decir dónde se debe aplicar la regla.
    deriving (Show, Eq)

-- Tipo de prueba.
data TypeProof = Direct -- ^ Prueba directa.
               | Cases  -- ^ Prueba por casos.
               | Induction -- ^ Prueba por inducción.
               | Deduction -- ^ Usando metateorema de la deducción.
    deriving (Show, Eq)

data Explicit = Initial 
              | Relation 
              | Final
    deriving (Show, Eq, Ord)

-- Conjunto de informacion a mostar relacionada con el objetivo del ejercicio.
type ExplicitInfo = S.Set Explicit

-- Determina de que manera la teoria esta disponible.
data AvaibleTheory = AvaibleTheory { name :: Text -- ^ Nombre de la teoria.
                                   , axioms :: [Axiom] -- ^ Axiomas a mostrar.
                                   , theos :: [Theorem] -- ^ Teoremas a mostrar.
                                   }

-- Lista de las teorias permitidas.
type AvaibleTheories = [AvaibleTheory]

-- Configuracion de un ejercicio.
data ExerciseConf = ExerciseConf { eConfTypeProof :: TypeProof
                                 , eConfExplicit :: ExplicitInfo
                                 , eConfRewriteMode :: RewriteMode
                                 , eConfTypeCheck :: TypeCheck
                                 , eConfAvaibleTheories :: AvaibleTheories
                                 , eConfInitCtx :: Ctx
                                 }

instance Show ExerciseConf where
    show exerConf = show (eConfTypeProof exerConf) ++ " " ++ 
                    show (eConfRewriteMode exerConf) ++ " " ++
                    show (eConfTypeCheck exerConf)

createExerciseConf :: ExerciseConf
createExerciseConf = ExerciseConf Direct S.empty Simple Auto [] M.empty 

typeCheckOptionList :: [TypeCheck]
typeCheckOptionList = [Auto, Manual, Infer]

rewriteModeOptionList :: [RewriteMode]
rewriteModeOptionList = [Simple, List, Focus]

typeProofOptionList :: [TypeProof]
typeProofOptionList = [Direct, Cases, Induction, Deduction]

explicitOptionList :: [Explicit]
explicitOptionList = [Initial, Relation, Final]
