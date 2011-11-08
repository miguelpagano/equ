-- | Test correspondientes a las reglas de re-escritura.
{-# Language OverloadedStrings #-}
module TestSuite.Tests.Matching where

import qualified Data.Map as M
import qualified Data.Sequence as S

import TestSuite.Tests.Parser

import Equ.Matching
import Equ.Parser
import Equ.PreExpr
import Equ.Theories.FOL(folForall,folExist)
import Test.HUnit (Assertion, assertFailure)
import Test.Framework (testGroup, Test)
import Test.Framework.Providers.HUnit (testCase)

import Control.Monad (unless)

-- | True v False -m-> p v p : No existe match.
testCase0 :: Assertion
testCase0 = testMatch lhs rhs res
    where lhs = pVp
          rhs = trueVfalse
          Just frhs =  goDown (toFocus rhs) >>= goRight
          merror = (frhs, DoubleMatch p true false)
          res = Left (merror, S.fromList [])

-- | True v False -m-> p v q : [p->True, q->False]
testCase1 :: Assertion
testCase1 = testMatch pVq trueVfalse (Right s)
    where s = M.insert p true (M.insert q false M.empty)

-- | Sy + S(x+S0) + z -m-> x + Sy + z : [x->Sy, y->x+S0]
testCase2 :: Assertion
testCase2 = testMatch xPlusSyPlusZ sAppyPlusSomePlusz  (Right s)
    where s = M.insert x sAppy (M.insert y xPlussApp0 M.empty)

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
testCase4 = testMatch lhs rhs res
    where lhs = parser "〈∀ x :〈∀ y : y = x : F@y@x〉: G@x〉"
          rhs = parser "〈∀ z :〈∀ z : z = z : F@z@z〉: G@z〉"
          Just frhs =  goDown (toFocus rhs) >>= goDown >>= goDown >>= goRight
          merror = (frhs, BindingVar v0)
          res = Left (merror, S.fromList [])


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
testCase7 = testMatch lhs rhs res
    where lhs = parser "R@y + x"
          rhs = parser "S@y + z"
          r = parser "R"
          s = parser "S"
          Just frhs = goDown (toFocus rhs) >>= goDown
          merror = (frhs, InequPreExpr r s)
          res = Left (merror, S.fromList [])


-- No deberiamos poder hacer matching de distintos cuantificadores.
testCase8 :: Assertion
testCase8 = testMatch lhs rhs res
    where lhs = parser "〈∃ x : x = F@x: xs↓1 = ys↓1〉"
          rhs = parser "〈∀ x : x = F@x: xs↓1 = ys↓1〉"
          frhs = toFocus rhs
          merror = (frhs, InequQuantifier folExist folForall)
          res = Left (merror, S.fromList [])


-- No deberiamos poder hacer matching de distintas constantes.
testCase9 :: Assertion
testCase9 = testMatch conL conR res
    where conL = parser "[]"
          conR = parser "0"
          fconR = toFocus conR
          merror = (fconR, InequPreExpr conL conR)
          res = Left (merror, S.fromList [])

-- | Controla que el matching entre las expresiones sea el correcto.
-- Toma dos expresiones y una substitución esperada.
testMatch :: PreExpr -> PreExpr -> Either (MatchMErr,Log) ExprSubst -> Assertion
testMatch pe pe' mpe = let m = match pe pe'
                       in unless (m == mpe) $
                            assertFailure $ 
                            "\n Resultado esperado: " ++ show mpe ++
                            "\n Contra : " ++ show m

-- | Grupo de test para matching.
testGroupMatch :: Test
testGroupMatch = testGroup "Matching" 
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
                 , testCase ("〈∃ ys : 〈∀ z : z = ys.0 : F@y ∧ (True ⇒ p ∨ q)〉 : ys↓1 = (xs++zs)↓1〉 -m-> \n" ++
                            "〈∃ xs : 〈∀ y : y = xs.0 : F@y ∧ p〉 : xs↓1 = ys↓1〉 :"++
                            "[p -> True ⇒ p ∨ q, ys -> (xs++zs)]")
                    testCase6
                 , testCase ("((True ∨ False) ∧ r) ⇒ (p ≡ q) -m-> " ++
                            "(p ⇒ q) :" ++
                            "[p -> ((True ∨ False) ∧ r), q -> (p ≡ q)]")
                    testCaseParens
                 , testCase "S@y + x -m-> R@y + x : No existe match."
                    testCase7
                 , testCase "∀ =/= ∃ : No existe match."
                    testCase8
                 , testCase "Constantes distintas; [] vs 0 : No existe match."
                    testCase9
                 ]
