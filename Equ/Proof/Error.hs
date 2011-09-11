module Equ.Proof.Error where

import Equ.Rule (Relation)
import Equ.Rewrite (RewriteError)
import Equ.Proof.Proof

-- Faltaría definir un buen conjunto de errores para las pruebas.
data ProofError = Rewrite RewriteError 
                | IncompatibleRels Relation Relation
                | BasicNotApplicable Basic
                | ProofError
    deriving Show
