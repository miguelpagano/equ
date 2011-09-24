module Equ.Proof.Monad where

import Equ.Proof.Error
import Equ.Proof.Proof

import Equ.Rewrite(RM)
import Equ.PreExpr
import Equ.Rule

type PM a = Either ProofError a

whenPM :: (a -> Bool) -> ProofError -> a -> PM a
whenPM p e a | p a      = return a
            | otherwise = Left e

liftRw :: RM a -> PM a
liftRw (Left err) = Left $ Rewrite err
liftRw (Right a) = return a

getCtx :: Proof -> PM Ctx
getCtx Reflex = Left ReflexHasNoCtx
getCtx (Hole c _ _ _) = Right c
getCtx (Simple c _ _ _ _) = Right c
getCtx (Trans c _ _ _ _ _ _) = Right c
getCtx (Cases c _ _ _ _ _) = Right c
getCtx (Ind c _ _ _ _ _) = Right c
getCtx (Deduc c _ _ _) = Right c
getCtx (Focus c _ _ _ _) = Right c


-- DUDA: Que hacemos con Reflex aca??
getStart :: Proof -> PM Focus
getStart Reflex = Left ReflexHasNoStart
getStart (Hole _ _ f _) = Right f
getStart (Simple _ _ f _ _) = Right f
getStart (Trans _ _ f _ _ _ _) = Right f
getStart (Cases _ _ f _ _ _) = Right f
getStart (Ind _ _ f _ _ _) = Right f
getStart (Deduc _ f _ _) = Right f
getStart (Focus _ _ f _ _) = Right f

getEnd :: Proof -> PM Focus
getEnd Reflex = Left ReflexHasNoEnd
getEnd (Hole _ _ _ f) = Right f
getEnd (Simple _ _ _ f _) = Right f
getEnd (Trans _ _ _ _ f _ _) = Right f
getEnd (Cases _ _ _ _ f _) = Right f
getEnd (Ind _ _ _ f _ _) = Right f
getEnd (Deduc _ _ f _) = Right f
getEnd (Focus _ _ _ f _) = Right f

-- | Devuelve la relación para la cual es una prueba.
getRel :: Proof -> PM Relation
getRel Reflex = Left ReflexHasNoRel
getRel (Hole _ r _ _) = Right r
getRel (Simple _ r _ _ _) = Right r
getRel (Trans _ r _ _ _ _ _) = Right r
getRel (Cases _ r _ _ _ _) = Right r
getRel (Ind _ r _ _ _ _) = Right r
getRel (Deduc _ _ _ _) = Right relImpl
getRel (Focus _ r _ _ _) = Right r
