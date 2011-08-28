-- | Test correspondientes a las reglas de re-escritura.
{-# Language OverloadedStrings #-}
module TestSuite.Tests.Matching where

import qualified Data.Map as M

import Equ.Matching
import Equ.Parser
import Equ.PreExpr
import Equ.Types
import Equ.Theories.FOL(folForall,folExist)
import Test.HUnit (Assertion, assertFailure)
import Test.Framework (testGroup, Test)
import Test.Framework.Providers.HUnit (testCase)

-- Variables para utilizar.
p :: Variable
p = var "p" TyUnknown
q :: Variable
q = var "q" TyUnknown
x :: Variable
x = var "x" TyUnknown
y :: Variable
y = var "y" TyUnknown
z :: Variable
z = var "z" TyUnknown
w :: Variable
w = var "w" TyUnknown
ys :: Variable
ys = var "ys" TyUnknown

-- | True v False -m-> p v p : No existe match.
testCase0 :: Assertion
testCase0 = testMatch lhs rhs (Left $ DoubleMatch p (parser "True") (parser "False"))
    where lhs = parser "p ∨ p"
          rhs = parser "True ∨ False"

-- | True v False -m-> p v q : [p->True, q->False]
testCase1 :: Assertion
testCase1 = testMatch (parser "p ∨ q") (parser "True ∨ False") (Right s)
    where s = M.insert p (parser "True") (M.insert q (parser "False") M.empty)

-- | Sy + S(x+S0) + z -m-> x + Sy + z : [x->Sy, y->x+S0]
testCase2 :: Assertion
testCase2 = testMatch (parser "x + S@y + z") (parser "S@y + S@(x+S@0) + z") (Right s)
    where s = M.insert x (parser "S@y") (M.insert y (parser "(x+S@0)") M.empty)

-- | #([0] ++ [1]) + 1 -m-> #([x,y]) + z : [x->0, y->1, z->1]
testCase3 :: Assertion
testCase3 = testMatch (parser "#([x] ++ [y,w]) + z")
                      (parser "#([0] ++ [1,2]) + 1") (Right s)
    where s = M.fromList [ (x, parser "0")
                         , (y, parser "1")
                         , (w, parser "2")
                         , (z, parser "1")
                         ]

-- | 〈∀ z : 〈∀ z : z = z : F@z@z〉 : G@z〉 -m->
--   〈∀ x : 〈∀ y : y = x : F@y@x〉 : G@x〉 : No existe match.
testCase4 :: Assertion
testCase4 = testMatch (parser "〈∀ x :〈∀ y : y = x : F@y@x〉: G@x〉")
                      (parser "〈∀ z :〈∀ z : z = z : F@z@z〉: G@z〉") 
                      (Left $ BindingVar x)

-- | 〈∃ xx : (G@(# []) + xx) ▹ [] ⇒ True : w ⇒ q〉 -m->
--   〈∃ x : G@y + x ▹ [] ⇒ p : q ⇒ w〉 : [y->(# []), p->True , w->q, q->w]
testCase5 :: Assertion
testCase5 = testMatch (parser "〈∃ x : G@y + x ▹ [] ⇒ p : q ⇒ w〉")
                      (parser "〈∃ xx : (G@(# []) + xx) ▹ [] ⇒ True : w ⇒ q〉") 
                      (Right s)
    where s = M.fromList [ (y, parser "(# [])")
                         , (p, parser "True")
                         , (w, parser "q")
                         , (q, parser "w")
                         ]

-- Uno mas complicado con cuantificadores. Dejamos libre en la segunda expresion
-- una variable que es ligada en la primera.
testCase6 :: Assertion
testCase6 = testMatch (parser "〈∃ xs : 〈∀ y : y = xs.0 : F@y ∧ p〉 : xs↓1 = ys↓1〉")
                      (parser "〈∃ ys : 〈∀ z : z = ys.0 : F@z ∧ (True ⇒ p ∨ q)〉 : ys↓1 = (xs++zs)↓1〉")
                      (Right s)
    where s = M.fromList [ (p,parser "(True ⇒ p ∨ q)")
                         , (ys,parser "(xs++zs)")
                         ]

testCaseParens :: Assertion
testCaseParens = testMatch (parser "(p ⇒ q)") (parser "((True ∨ False) ∧ r) ⇒ (p ≡ q)")
                 (Right s)
    where s = M.fromList [ (p,parser "((True ∨ False) ∧ r)")
                         , (q,parser "(p ≡ q)")
                         ]

-- No deberiamos poder hacer matching de funciones con nombres distintos.
testCase7 :: Assertion
testCase7 = testMatch lhs rhs (Left $ InequPreExpr (parser "R@y") (parser "S@y"))
    where lhs = parser "R@y + x"
          rhs = parser "S@y + z"

-- No deberiamos poder hacer matching de distintos cuantificadores.
testCase8 :: Assertion
testCase8 = testMatch (parser "〈∃ x : x = F@x: xs↓1 = ys↓1〉")
                      (parser "〈∀ x : x = F@x: xs↓1 = ys↓1〉")
                      (Left $ InequQuantifier folExist folForall)
                                            

-- No deberiamos poder hacer matching de distintas constantes.
testCase9 :: Assertion
testCase9 = testMatch conL conR $ Left (InequPreExpr conL conR)
    where conL = parser "[]"
          conR = parser "0"


-- | Controla que el matching entre las expresiones sea el correcto.
-- Toma dos expresiones y una substitución esperada.
testMatch :: PreExpr -> PreExpr -> Either MatchError ExprSubst -> Assertion
testMatch pe pe' mpe = let m = match pe pe'
                       in if m == mpe 
                             then return ()
                             else assertFailure $ 
                                    "\n Resultado esperado: " ++ show mpe ++
                                    "\n Contra : " ++ show m

-- | Grupo de test para matching.
testGroupMatch :: Test
testGroupMatch = 
    testGroup "Matching" 
    [ testCase "True v False -m-> p v p : No existe match." 
        testCase0
    , testCase "True v False -m-> p v q : [p->True, q->False]"
        testCase1
    , testCase "Sy + S(x+S0) + z -m-> x + Sy + z : [x->Sy, y->x+S0]"
        testCase2
    , testCase "#([0] ++ [1]) + 1 -m-> #([x,y]) + z : [x->0, y->1, z->1]"
        testCase3
    , testCase ("〈∀ z : 〈∀ z : z = z : F@z@z〉 : G@z〉 -m->" ++ 
                "〈∀ x : 〈∀ y : y = x : F@y@x〉 : G@x〉  :" ++ 
                "No exite match.")
        testCase4
    , testCase ("〈∃ xx : (G@(# []) + xx) ▹ [] ⇒ True : w ⇒ q〉 -m-> " ++
                "〈∃ x : G@y + x ▹ [] ⇒ p : q ⇒ w〉 :" ++
                "[y->(# []), p->True , w->q, q->w]")
        testCase5
    , testCase ("〈∃ ys : 〈∀ z : z = ys.0 : F@y ∧ (True ⇒ p ∨ q)〉 : ys↓1 = (xs++zs)↓1〉 -m->" ++
                "〈∃ xs : 〈∀ y : y = xs.0 : F@y ∧ p〉 : xs↓1 = ys↓1〉 :"++
                "[p -> True ⇒ p ∨ q, ys -> (xs++zs)]")
        testCase6
    , testCase ("((True ∨ False) ∧ r) ⇒ (p ≡ q) -m-> " ++
                      "(p ⇒ q) :" ++
                      "[p -> ((True ∨ False) ∧ r), q -> (p ≡ q)]")
        testCaseParens
                
    ]