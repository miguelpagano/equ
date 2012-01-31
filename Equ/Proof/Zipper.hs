module Equ.Proof.Zipper 
    ( ProofFocus
    , ProofPath(..)
    , toProof, toProofFocus
    , replace
    , goDown, goUp, goLeft, goRight, goDownR, goDownL, goTop
    -- las siguientes funcionas navegan el zipper y siempre devuelven algo
    , goDown', goUp', goLeft', goRight', goDownR', goDownL', goTop', goEnd
    , moveToEnd, goFirstLeft, goLeftLeaf, goNextStep, goFirstRight, goRightLeaf
    , goPrevStep
    ) where

import Equ.Proof.Proof
import Data.Monoid
import Data.Maybe(fromJust)

-- | Definición de los posibles lugares en los que podemos estar
-- enfocándonos.
data ProofPath = Top
               | TransL ProofPath Proof
               | TransR Proof ProofPath
            deriving (Eq,Show)

            
type ProofFocus = (Proof,ProofPath)

toProof :: ProofFocus -> Proof
toProof (p, Top) = p
toProof (p, TransL path pr) = toProof (mappend p pr,path)
toProof (p, TransR pl path) = toProof (mappend pl p,path)

toProofFocus :: Proof -> ProofFocus
toProofFocus p = (p,Top)

-- | Reemplaza la expresión enfocada por una nueva expresión.
replace :: ProofFocus -> Proof -> ProofFocus
replace (_,p) p' = (p',p)

-- | Bajar un nivel en el focus, yendo por izquierda.
goDownL :: ProofFocus -> Maybe ProofFocus
goDownL = goDown

goDownL' :: ProofFocus -> ProofFocus
goDownL' = goDown'

-- | Bajar un nivel en el focus, yendo por derecha.
goDownR :: ProofFocus -> Maybe ProofFocus
goDownR f = goDown f >>= goRight

goDownR' :: ProofFocus -> ProofFocus
goDownR' = goRight' . goDown'

-- Navegación dentro de un Zipper.
-- | Bajar un nivel en el focus.
goDown :: ProofFocus -> Maybe ProofFocus
goDown (Trans _ _ _ _ _ pl pr,path) = Just (pl,TransL path pr)
goDown (_,_)= Nothing

goDown' :: ProofFocus -> ProofFocus
goDown' (Trans _ _ _ _ _ pl pr,path) = (pl,TransL path pr)
goDown' pf= pf

-- | Subir un nivel en el focus.
goUp :: ProofFocus -> Maybe ProofFocus
goUp (_, Top) = Nothing
goUp (p, TransL path pr) = Just (mappend p pr,path)
goUp (p, TransR pl path) = Just (mappend pl p,path)

goUp' :: ProofFocus -> ProofFocus
goUp' (p, TransL path pr) = (mappend p pr,path)
goUp' (p, TransR pl path) = (mappend pl p,path)
goUp' pf = pf

-- | Sube hasta el tope.
goTop :: ProofFocus -> Maybe ProofFocus
goTop (p,Top) = Just (p,Top)
goTop pf = goTop $ fromJust $ goUp pf

goTop' :: ProofFocus -> ProofFocus
goTop' (p,Top) = (p,Top)
goTop' pf = goTop' $ goUp' pf

-- | Se mueve a la derecha todo lo q pueda.
goEnd :: ProofFocus -> ProofFocus
goEnd pf = case (goDownR pf) of
                Nothing -> pf
                Just pf' -> goEnd pf'

-- | Ir a la izquierda en un focus, sin cambiar de nivel.
goLeft :: ProofFocus -> Maybe ProofFocus
goLeft (p, TransR pl path) = Just (pl,TransL path p)
goLeft (_, _) = Nothing

goLeft' :: ProofFocus -> ProofFocus
goLeft' (p, TransR pl path) = (pl,TransL path p)
goLeft' pf = pf

{- | Se Mueve arriba desde la derecha, lo mas que puede, hasta llegar a un nodo
     que esta en la parte izquierda: 
-}
goFirstLeft :: ProofFocus -> ProofFocus
goFirstLeft pf = case (goRight pf) of
                      Nothing -> case (goUp pf) of
                                      Nothing -> pf
                                      Just pf' -> goFirstLeft pf'
                      Just pf' -> pf
               
-- | Simétrica a goFirstLeft
goFirstRight :: ProofFocus -> ProofFocus
goFirstRight pf = case (goLeft pf) of
                      Nothing -> case (goUp pf) of
                                      Nothing -> pf
                                      Just pf' -> goFirstRight pf'
                      Just pf' -> pf                       
                      
-- | Baja a la hoja de mas a la izquierda
goLeftLeaf :: ProofFocus -> ProofFocus
goLeftLeaf pf = case (goDownL pf) of
                     Nothing -> pf
                     Just pf' -> goLeftLeaf pf'
               
-- | Baja a la hoja de mas a la derecha
goRightLeaf :: ProofFocus -> ProofFocus
goRightLeaf pf = case (goDownR pf) of
                     Nothing -> pf
                     Just pf' -> goRightLeaf pf'

-- | Ir a la derecha en un focus, sin cambiar de nivel.
goRight :: ProofFocus -> Maybe ProofFocus
goRight (p, TransL path pr) = Just (pr,TransR p path)
goRight (_, _) = Nothing

goRight' :: ProofFocus -> ProofFocus
goRight' (p, TransL path pr) = (pr,TransR p path)
goRight' pf = pf

{- | La siguiente funcion mueve el focus hasta la siguiente hoja de la prueba.
     En una transitividad, vista como lista: [p1,...,pn]. goNextStep pi = pi+1.
     NOTA: Tal como está ahora, si estamos en la ultima hoja, vuelva a la primera.
     -}
goNextStep :: ProofFocus -> ProofFocus
goNextStep = goLeftLeaf . goRight' . goFirstLeft

goPrevStep :: ProofFocus -> ProofFocus
goPrevStep = goRightLeaf . goLeft' . goFirstRight

moveToEnd :: ProofFocus -> Maybe ProofFocus
moveToEnd = Just . goEnd . goTop'
