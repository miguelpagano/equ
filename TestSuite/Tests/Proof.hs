module TestSuite.Tests.Proof (
            prop_serialization
            )
    where

import Equ.Proof

prop_serialization :: Proof -> Bool
prop_serialization p = p == (decode . encode) p
