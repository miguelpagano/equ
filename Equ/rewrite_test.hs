import qualified Data.Map as M
import Data.Text

import Equ.PreExpr.Internal
import Equ.Syntax
import Equ.Rule
import Equ.Expr
import Equ.Parser
import Equ.Theories.FOL
import Equ.Rewrite
import Equ.Types
import Prelude hiding (or,and)

test1 = match [] (parser "p ∨ p") (parser "True ∨ False") M.empty
test2 = match [] (parser "x + S@y+z") (parser "S@y + S@(x+S@0)+z") M.empty
test3 = match [] (parser "succ x * (x * y)") (parser "succ (e*x) * ((e*z) * y)") M.empty


-- TEST SENCILLOS:
rewrite_test01 = exprRewrite (Expr $ parser "F@a ⇒ True") implRule2

-- distEqOr_Rule1: p ∨ (q ≡ r) ≡ ((p ∨ q) ≡ (p ∨ r))
rewrite_test02 = exprRewrite (Expr $ parser "F@a ∨ (False ≡ r)") distEqOr_Rule1
match_test02 = match [] (parser "p ∨ (q ≡ r)") (parser "F@a ∨ (False ≡ r)") M.empty

-- este test lo hago porq no esta matcheando el lado izquierdo de la regla distEqOr_Rule1 con la expresion
-- p ∨ (q ≡ r), la unica diferencia entre ambas expresiones es q la de la regla no tiene parentesis en el equivalente
rewrite_test03 = match [] (getPreExpr $ or (Expr $ parser "p") (equiv (Expr $ parser "q") (Expr $ parser "r")))
                       (getPreExpr $ or (Expr $ parser "p") (Expr $ Paren $ getPreExpr $ equiv (Expr $ parser "q") (Expr $ parser "r")))
                        M.empty

-- TESTS MAS COMPLICADOS:
str1 = "((F@(succ 0) + x) ▹ [] ⇒ True)"
str2 = "((G@(# []) + x) ▹ [] ⇒ True ∨ p ⇒ q)"

rewrite_test1 = exprRewrite (Expr $ parser $ str1 ++ "∨" ++str1) idempotOr_Rule
rewrite_test2 = exprRewrite (Expr $ parser (str1 ++ "∧" ++str2)) goldenRule1


exp1= parser "〈∃ x : (G@(# []) + x) ▹ [] ⇒ True : w ⇒ q〉"
testFreeVars = freeVars (exp1)
testFreshVar= freshVar (freeVars exp1)
testQuants= match [] (parser "〈∀ x : x = z : F@x〉") (parser "〈∀ z : z = F@a : F@z〉") M.empty

testQ2 = match [] (parser "〈∀ x : 〈∀ y : y = x : F@y@x〉 : G@x〉") (parser "〈∀ z : 〈∀ z : z = z : F@z@z〉 : G@z〉") M.empty

-- /////////// Algunos casos que probe para substitution2.
x = var "x" TyUnknown 
y = var "y" TyUnknown 
q = var "q" TyUnknown 

pe = parser "〈∃ a: (〈∃ z: F@z : F@a〉) : F@x〉"
spe = substitution2 x y pe

pe1 = parser "〈∃ x : (G@(# []) + x) ▹ [] ⇒ True : w ⇒ q〉"
spe1 = substitution2 q x pe1
spe2 = substitution2 x q pe1

pe2 = parser "F@x = True ∨ x ⇒ y"
spe3 = substitution2 x y pe2
-- /////////// Algunos casos que probe para substitution2.


{- Mas test de reescritura -}
-- Intercambio entre rango y término: <∀x : r.x : f.x> ≡ <∀x : : r.x ⇒ f.x>

testR= exprRewrite (Expr $ parser "〈∀ xs : # xs = 0 : [] ↓ n = []〉") interRangeTermForall_Rule
