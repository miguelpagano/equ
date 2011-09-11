module Equ.Proof.Monad where

import Equ.Proof.Error
import Equ.Rewrite(RM)
type PM a = Either ProofError a

whenPM :: (a -> Bool) -> ProofError -> a -> PM a
whenPM p e a | p a      = return a
            | otherwise = Left e

liftRw :: RM a -> PM a
liftRw (Left err) = Left $ Rewrite err
liftRw (Right a) = return a