-- | Declaración de test-suites.
module Main where

import TestSuite.Tests.TypeChecker
import TestSuite.Tests.Matching
import TestSuite.Tests.PreExpr
import TestSuite.Tests.Proof
import TestSuite.Tests.Rules
import Test.Framework (defaultMain, testGroup, Test)
import Test.Framework.Providers.QuickCheck2 (testProperty)

main :: IO ()
main = defaultMain tests

-- Conjunto de casos de test.
tests :: [Test]
tests = [ testGroup "PreExpr" 
                [ testProperty "forall t \\in toFocuses pe, toExpr t = pe" 
                                prop_toFocuses
                ]
        , testGroup "TypeChecker"
                [ testProperty "Unification Algorithm" prop_unification
                , testProperty "Generation of Fresh Type-Variables" prop_freshVars
                ]
        , testListRules 
        , testGroupMatch
        , testGroupProof
        ]
