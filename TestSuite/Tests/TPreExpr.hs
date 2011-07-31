module TestSuite.Tests.TPreExpr (
                prop_toFocuses
                )
    where

import Equ.PreExpr

-- Checkea que (forall e):
--   forall t \in toFocuses e, toExpr t = e
prop_toFocuses :: PreExpr -> Bool
prop_toFocuses pe = prop_toFocusesAux pe (toFocuses pe)

-- Auxiliar para checkear la propiedad de arriba.
prop_toFocusesAux :: PreExpr -> [Focus] -> Bool
prop_toFocusesAux pe [] = True
prop_toFocusesAux pe (f:fs) | toExpr f == pe = prop_toFocusesAux pe fs
                            | otherwise = False
