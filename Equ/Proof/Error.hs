module Equ.Proof.Error where

import Equ.Rule (Relation)
import Equ.Rewrite (RewriteError)
import Equ.Proof.Zipper(ProofFocus)
import Equ.Proof.Proof

-- | Errores sobre las pruebas.
-- El error contiene informacion sobre en que lugar de la prueba se produjo el error.
-- La función navega en el ProofFocus correspondiente a la prueba, desde el tope.
data ProofError = ProofError ProofError' (ProofFocus -> ProofFocus)

instance Eq ProofError where
    (==) (ProofError er _) (ProofError er' _) = er == er'
                
instance Show ProofError where
    show (ProofError p m) = show p
    
data ProofError' = Rewrite [RewriteError]
                | BasicNotApplicable Basic
                | HoleProof        -- Prueba vacía.
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
                | TransInconsistent Proof -- Una prueba transitiva donde los focuses 
                                     --no coinciden con las pruebas
                | DeducInvalidEnd -- En un uso del meta-teorema de la deducción
                                  -- no coincide el final de la prueba interior
                                  -- con el esperado
                | InductionError PErrorInduction
                | ContextsNotEqual -- El contexto de una subprueba no es el mismo de la prueba general.
                | RelNotEqual -- Las relaciones entre dos pruebas no son iguales
                | Error
    deriving Eq
    
data PErrorInduction = 
                       IndInNotVar -- Se quiere hacer inducción sobre una expresión que no es variable.
                     | VarNotInExpr -- La variable sobre la q se hace induccion no está en las expresiones
                     | TypeNotInductive -- El tipo de la variable sobre la q se hace inducción no es inductivo.
                     | SubProofHypothesis -- Una subprueba agrega hipótesis no válidas.
                     | ConstantPatternError -- La constante no es un pattern del tipo inductivo
                     | OperatorPatternError -- El operador no es un pattern del tipo inductivo
                     
                     
instance Show ProofError' where
    show (Rewrite r) = "Error de reescritura: "++ show r
    show (BasicNotApplicable b) = "No se puede aplicar el paso básico: "++ show b
    show HoleProof = "La prueba tiene un hueco"
    show (ClashCtx c1 c2) = "Los contextos no coinciden: "++ show c1 ++ ", " ++ show c2
    show (ClashRel r1 r2) = "Las relaciones no coinciden: "++ show r1 ++ ", "++show r2
    show (ClashAddStep p1 p2) = "No es posible agregar paso"
    show (ProofEndWithHole p) = "La prueba no puede terminar en hueco"
    show (ClashProofNotHole p) = "La prueba " ++ show p ++" debe ser un hueco"
    show ReflexHasNoCtx = "Una prueba reflexiva no debe tener contexto"
    show ReflexHasNoStart = "Una prueba reflexiva no debe tener expresión inicial"
    show ReflexHasNoEnd = "Una prueba reflexiva no debe tener expresión final"
    show ReflexHasNoRel = "Una prueba reflexiva no debe tener relación"
    show (TransInconsistent p) = "La prueba transitiva es inconsistente: " ++ show p
    show (DeducInvalidEnd) = unlines [ "En un uso del meta-teorema de la deducción"
                                     , "no coincide el final de la prueba interior"
                                     , "con el esperado"]
    
                                     
    show (InductionError er) = "Error en Prueba Inductiva: "++ show er
    show (ContextsNotEqual) = "La subprueba no tiene el mismo contexto que la prueba general"
    show (RelNotEqual) = "La subprueba no tiene la misma relación que la prueba general"
    show _ = "Error sin especificar"

instance Show PErrorInduction where
    show (IndInNotVar) = "Solo se puede hacer inducción en variables."
    show (VarNotInExpr) = "La variable sobre la que se hace inducción debe ocurrir en la primera expresión de la prueba"
    show (TypeNotInductive) = "El tipo de la variable sobre la que se hace inducción debe ser inductivo"
    show (SubProofHypothesis) = "Las subpruebas no pueden agregar hipótesis extras, salvo la inductiva en caso de q corresponda"
    show (ConstantPatternError) = "La constante no es un constructor del tipo inductivo"
    show (OperatorPatternError) = "El operador no es un constructor del tipo inductivo"

errEmptyProof :: ProofError
errEmptyProof = ProofError HoleProof id

getMoveFocus :: ProofError -> (ProofFocus -> ProofFocus)
getMoveFocus (ProofError _ move) = move

errProof :: ProofError
errProof = ProofError Error id
    