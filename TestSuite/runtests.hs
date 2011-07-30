module Main where

import Tests.TPreExpr
import Test.Framework (defaultMainWithArgs, testGroup)
import Test.Framework.Providers.QuickCheck2 (testProperty)

main = defaultMainWithArgs tests ["--maximum-generated-tests=5000"]

-- Conjunto de casos de test.
tests = [
            testGroup "PreExpr properties" [
                testProperty "forall t \\in toFocuses pe, toExpr t = pe" 
                    prop_toFocuses
            ]
        ]
