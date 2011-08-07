-- | Test correspondientes a las reglas de re-escritura.
module TestSuite.Tests.TRules where

import Equ.Theories
import Equ.Expr
import Equ.TypeChecker
import Equ.Rule(Rule(..))
import Data.Traversable
import Data.Text (unpack)
import Test.HUnit (Assertion, assertFailure)
import Test.Framework (testGroup, Test)
import Test.Framework.Providers.HUnit (testCase)

-- | Controla que una expresión esté bien tipada.
testTypeable :: Expr -> Assertion
testTypeable (Expr e) = case checkPreExpr e of 
                          Left _ -> assertFailure $ "No se pudo tipar la expresión: " ++ show e
                          Right _ -> return ()

-- TODO: Verificar que los tipos son iguales.
-- | Controla que los dos lados de una regla estén bien tipados.
testRule :: Rule -> Test
testRule r = testGroup ("Regla: " ++ nameRule) 
               [ testCase "Lado izquierdo: " . testTypeable $ lhs r
               , testCase "Lado derecho: "   . testTypeable $ rhs r
               ] 
    where nameRule = unpack $ name r

-- TODO: Extenderlo a las otras teorías.
-- | Aplica 'testRule' a todas las reglas de una teoría.
testListRules :: Test
testListRules = testGroup "Teoría de Listas" $ map testRule listRules