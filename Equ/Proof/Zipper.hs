module Equ.Proof.Zipper 
    ( ProofFocus
    , ProofPath
    , toProof, toProofFocus
    , replace
    , goDown, goUp, goLeft, goRight, goDownR, goDownL
    ) where

import Equ.Proof.Proof
import Data.Monoid

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

-- Bajar un nivel en el focus, yendo por izquierda.
goDownL :: ProofFocus -> Maybe ProofFocus
goDownL = goDown

-- Bajar un nivel en el focus, yendo por derecha.
goDownR :: ProofFocus -> Maybe ProofFocus
goDownR f = goDown f >>= goRight

-- Navegación dentro de un Zipper.
-- | Bajar un nivel en el focus.
goDown :: ProofFocus -> Maybe ProofFocus
goDown (Trans _ _ _ _ _ pl pr,path) = Just (pl,TransL path pr)
goDown (_,_)= Nothing

-- | Subir un nivel en el focus.
goUp :: ProofFocus -> Maybe ProofFocus
goUp (_, Top) = Nothing
goUp (p, TransL path pr) = Just (mappend p pr,path)
goUp (p, TransR pl path) = Just (mappend pl p,path)

-- | Ir a la izquierda en un focus, sin cambiar de nivel.
goLeft :: ProofFocus -> Maybe ProofFocus
goLeft (p, TransR pl path) = Just (pl,TransL path p)
goLeft (_, _) = Nothing

-- | Ir a la derecha en un focus, sin cambiar de nivel.
goRight :: ProofFocus -> Maybe ProofFocus
goRight (p, TransL path pr) = Just (pr,TransR p path)
goRight (_, _) = Nothing
