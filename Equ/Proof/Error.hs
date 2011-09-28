module Equ.Proof.Error where

import Equ.Rule (Relation)
import Equ.Rewrite (RewriteError)
import Equ.Proof.Proof

-- Faltaría definir un buen conjunto de errores para las pruebas.
data ProofError = Rewrite RewriteError                 
                | BasicNotApplicable Basic
                | BasicNotApplicable0 Basic
                | ProofError
                | ClashCtx Ctx Ctx -- Contextos distintos.
                | ClashRel Relation Relation -- Relaciones distintas
                | ClashAddStep Proof Proof -- Error al intentar agregar un paso.
                | ProofEndWithHole Proof -- Identifica una prueba que cuyo 
                                         -- final es un hueco de preExpr.
                | ClashProofNotHole Proof -- La prueba no es del tipo hueco.
                | ReflexHasNoCtx -- Reflex no tiene contexto.
                | ReflexHasNoStart -- Reflex no tiene prueba de inicio.
                | ReflexHasNoEnd -- Reflex no tiene prueba final.
                | ReflexHasNoRel -- Reflex no tiene relacion.
    deriving (Show, Eq)
