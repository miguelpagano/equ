module Equ.Exercise.Conf where

import Data.Text

import Equ.Proof

{- Auto: se hace automáticamente al parsear
   Manual: no se infiere nada, se hace a mano.
   Infer: se puede usar el botón “Inferir” en la caja del árbol.
-}
data TypeCheck = Auto | Manual | Infer

-- Tipo de re-escritura.
data RewriteMode = Simple -- ^ Directa.
                 | List     -- ^ Se puede ver la lista de resultados.
                 | Focus -- ^ Se debe decir dónde se debe aplicar la regla.

-- Tipo de prueba.
data TypeProof = Direct -- ^ Prueba directa.
               | Cases  -- ^ Prueba por casos.
               | Induction -- ^ Prueba por inducción.
               | Deduction -- ^ Usando metateorema de la deducción.


data Explicit = Initial | Relation | Final

-- Conjunto de informacion a mostar relacionada con el objetivo del ejercicio.
data ExplicitInfo = Set Explicit

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
