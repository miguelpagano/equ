module Equ.Proof.Monad where

import Equ.Proof.Error
import Equ.Proof.Proof hiding (getCtx, getStart, getEnd, getRel)
import qualified Equ.Proof.Proof as P ( getCtx, getStart
                                      , getEnd, getRel) 

import Equ.Rewrite(RM)
import Equ.PreExpr
import Equ.Rule


type PM a = Either [ProofError] a

whenPM :: (a -> Bool) -> ProofError -> a -> PM a
whenPM p e a | p a      = return a
             | otherwise = Left [e]

liftRw :: RM a -> PM a
liftRw (Left err) = Left $ [Rewrite err]
liftRw (Right a) = return a

-- Lifting de proyecciones de Proof a la mónada de Proof.
getCtx :: Proof -> PM Ctx
getCtx = maybe (Left [ReflexHasNoCtx]) return . P.getCtx

getStart :: Proof -> PM Focus
getStart = maybe (Left [ReflexHasNoStart]) return . P.getStart

getEnd :: Proof -> PM Focus
getEnd = maybe (Left [ReflexHasNoEnd]) return . P.getEnd

getRel :: Proof -> PM Relation
getRel = maybe (Left [ReflexHasNoRel]) return . P.getRel
