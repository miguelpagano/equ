-- | Declaración de test-suites.
module Main where

import TestSuite.Tests.TypeChecker
import TestSuite.Tests.Matching
import TestSuite.Tests.PreExpr
import TestSuite.Tests.Parser
import TestSuite.Tests.Proof
import TestSuite.Tests.Rules
import Test.Framework (defaultMain, testGroup, Test)
import Test.Framework.Providers.QuickCheck2 (testProperty)

main :: IO ()
main = defaultMain tests

-- Conjunto de casos de test.
tests :: [Test]
tests = [ -- Grupo de test para las preExpresiones.
          testGroup "PreExpr" 
                [ testProperty "forall t \\in toFocuses pe, toExpr t = pe" 
                                prop_toFocuses
                ]
        , -- Grupo de test del typeChecker.
          testGroup "TypeChecker"
                [ testProperty "Unification Algorithm" prop_unification
                , testProperty "Generation of Fresh Type-Variables" prop_freshVars
                ]
        , -- Grupo de test para las reglas.
          testListRules 
        , -- Grupo de test del parser.
          testGroupParse
        , -- Grupo de test de matching.
          testGroupMatch
        , -- Grupo de test de las pruebas.
          testGroupProof
        ]
