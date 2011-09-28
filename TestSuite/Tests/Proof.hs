module TestSuite.Tests.Proof (
            testGroupProof
            )
    where


import Test.Framework (testGroup, Test)
import Test.HUnit (Assertion, assertFailure)
import Test.Framework.Providers.HUnit (testCase)
import Test.Framework.Providers.QuickCheck2 (testProperty)

import Control.Monad (unless)

import qualified Data.Map as M (empty)

import Equ.Expr
import Equ.Rule
import Data.Text
import Equ.Proof
import Equ.Parser
import Equ.PreExpr
import Equ.Theories.FOL

-- | Test sobre serializacion; decode . encode == id
prop_serialization :: Proof -> Bool
prop_serialization p = let Right p' = (decode . encode) p in p == p'

-- Focus utilizados en Unit-Test.
f_Fx :: Focus
f_Fx = toFocus $ parser "F@x"
f_Fy :: Focus 
f_Fy = toFocus $ parser "F@y"
f_p :: Focus
f_p = toFocus $ parser "p"
f_y :: Focus
f_y = toFocus $ parser "y"
f_z :: Focus
f_z = toFocus $ parser "z"
f_Q0 :: Focus
f_Q0 = toFocus $ parser "〈∀ x : R@x ∨ S@x : T@x〉"
f_Q1 :: Focus
f_Q1 = toFocus $ parser "〈∀ x : R@x : T@x〉 ∧ 〈∀ x : S@x : T@x〉"
f_star0 :: Focus
f_star0 = toFocus $ parser "p ∨ q"
f_star1 :: Focus
f_star1 = toFocus $ parser "p ∨ ¬q ≡ p"
f_gr0 :: Focus
f_gr0 = toFocus $ parser "p ∧ q"
f_gr1 :: Focus
f_gr1 = toFocus $ parser "p ≡ q ≡ p ∨ q"
f_neu0 :: Focus
f_neu0 = toFocus $ parser "True ≡ p"
f_dm :: Focus
f_dm = toFocus $ parser "¬(p ∨ q)"
f_hole1 :: Focus
f_hole1 = toFocus $ preExprHole holeInfo1
f_hole0 :: Focus
f_hole0 = toFocus $ preExprHole holeInfo0

-- Pruebas utilizadas en unit-test.
p_Fx_Eq_Y :: Proof
p_Fx_Eq_Y = newProof relEq f_Fx f_y 
p_Fx_Eq_Z :: Proof
p_Fx_Eq_Z = newProof relEq f_Fx f_z
p_Z_Eq_Y :: Proof
p_Z_Eq_Y = newProof relEq f_z f_y
p_Y_Eq_Z :: Proof
p_Y_Eq_Z = newProof relEq f_y f_z
p_Fx_Impl_Z :: Proof
p_Fx_Impl_Z = newProof relImpl f_Fx f_z
p_Fy_Eq_Z :: Proof
p_Fy_Eq_Z = newProof relEq f_Fy f_z

-- Información en huecos de preExpr para unit-test.
holeInfo0 :: Text
holeInfo0 = pack ""
holeInfo1:: Text
holeInfo1 = pack "p ∨ ¬q"

-- Axiomas utilizados en unit-test.
axGoldenRule :: Axiom
axGoldenRule = Axiom {
                  axName = pack "Regla Dorada"
                , axExpr = Expr $ parser "p ∧ q ≡ p ≡ q ≡ p ∨ q"
                , axRel = relEquiv
                , axRules = [ goldenRule1, goldenRule2 
                            , goldenRule3, goldenRule4
                            , goldenRule5
                            ]
                }

axNeutralEquiv :: Axiom
axNeutralEquiv = Axiom { axName = pack "Neutro de la equivalencia"
                       , axExpr = Expr $ parser "p ≡ True ≡ p"
                       , axRel = relEquiv
                       , axRules = [neuterEquiv_Rule1, neuterEquiv_Rule2]
                       }
{- Todavía en proceso.

f_true :: Focus
f_true = toFocus $ parser "True"
f_pip0 :: Focus
f_pip0 = toFocus $ parser "p ⇒ p"
f_pip1 :: Focus
f_pip1 = toFocus $ parser "p ∨ q ≡ q"
f_q :: Focus
f_q = toFocus $ parser "q"


implRule2 :: Rule
implRule2 = Rule { lhs = f_pip0
                 , rhs = f_pip1
                 , rel = relEquiv
                 , name = ""
                 , desc = ""
                 }

axImpl :: Axiom
axImpl = Axiom { axName = pack "Regla implicacion"
               , axExpr = Expr $ parser "p ⇒ q ≡ p ∨ q ≡ q"
               , axRel = relEquiv
               , axRules = [implRule0, implRule1, implRule2]
               }

p_pip01 :: Proof
p_pip01 = Simple M.empty relEquiv f_pip0 f_pip1 (Ax axImpl)

p_pip12 :: Proof
p_pip12 = Simple M.empty relEquiv f_pip1 f_true (Ax axImpl)

p_P_Impl_P :: Proof
p_P_Impl_P = Trans M.empty relEquiv f_pip0 f_pip1 f_true p_pip01 p_pip12

-}

-- Pruebas usadas en unit-test.
p_Gr0 :: Proof
p_Gr0 = Simple M.empty relEquiv f_gr0 f_gr1 (Ax axGoldenRule)

p_Neu0 :: Proof
p_Neu0 = Simple M.empty relEquiv f_p f_neu0 (Ax axNeutralEquiv)

{- Prueba usando regla dorada.
    ((p)∧(q),Top)
Equiv {Ax "Regla Dorada": ((((p)∧(q))≡(p))≡(q))≡((p)∨(q))}
    (((p)≡(q))≡((p)∨(q)),Top)
-}
testCaseProofFromAxiom0 :: Assertion
testCaseProofFromAxiom0 = testCaseProofFromTruth f_gr0 f_gr1 relEquiv 
                                                 axGoldenRule (Right p_Gr0)

{- Prueba usando neutro de la equivalencia.
    (p,Top)
Equiv {Ax "Neutro de la equivalencia": ((p)≡(True))≡(p)}
    ((True)≡(p),Top)
-}
testCaseProofFromAxiom1 :: Assertion
testCaseProofFromAxiom1 = testCaseProofFromTruth f_p f_neu0 relEquiv 
                                                 axNeutralEquiv (Right p_Neu0)

-- Verificar casos de tests para pruebas con axiomas y teoremas.
testCaseProofFromTruth :: (Truth t) => Focus -> Focus -> Relation -> t
                          -> PM Proof -> Assertion
testCaseProofFromTruth f f' r t res = let p = proofFromTruth f f' r t
                                    in unless (p == res) $
                                        assertFailure $ 
                                        "\n Resultado esperado: " ++ show res ++
                                        "\n Contra: " ++ show p


{- Comenzar una prueba con la siguiente forma;
    (F (x),Top)
Eq  {?}
    (y, Top)
-}
testCaseNewProof0 :: Assertion
testCaseNewProof0 = testCaseNewProof relEq f_Fx f_y 
                        (Hole M.empty relEq f_Fx f_y)

{- Comenzar una prueba con la siguiente forma;
    〈∀ x : R@x ∨ S@x : T@x〉
Equiv  {?}
    〈∀ x : R@x : T@x〉 ∧ 〈∀ x : S@x : T@x〉
-}
testCaseNewProof1 :: Assertion
testCaseNewProof1 = testCaseNewProof relEquiv f_Q0 f_Q1 
                        (Hole M.empty relEquiv f_Q0 f_Q1)

{- Comenzar una prueba con la siguiente forma;
    p ∨ q
Equiv  {?}
    p ∨ ¬q ≡ p
-}
testCaseNewProof2 :: Assertion
testCaseNewProof2 = testCaseNewProof relEquiv f_star0 f_star1 
                        (Hole M.empty relEquiv f_star0 f_star1)

-- Verificar casos de tests para el comienzo de pruebas sin huecos de preExpr.
testCaseNewProof :: Relation -> Focus -> Focus -> Proof -> Assertion
testCaseNewProof r f f' res = let p = newProof r f f'
                              in unless (p == res) $
                                  assertFailure $ 
                                  "\n Resultado esperado: " ++ show res ++
                                  "\n Contra: " ++ show p

{- Comenzar una prueba con la siguiente forma;
    p ∨ q
Equiv  {?}
    ?{p ∨ ¬q}
-}
testCasenewProofWE0 :: Assertion
testCasenewProofWE0 = testCasenewProofWE relEquiv f_star0 holeInfo1
                            (Hole M.empty relEquiv f_star0 f_hole1)

{- Comenzar una prueba con la siguiente forma;
    ¬(p ∨ q)
Impli  {?}
    ?
-}
testCasenewProofWE1 :: Assertion
testCasenewProofWE1 = testCasenewProofWE relImpl f_dm holeInfo0
                            (Hole M.empty relImpl f_dm f_hole0)

-- Verificar casos de tests para el comienzo de una prueba sin final, es decir,
-- una prueba en la que tenemos un hueco de preExpr como expresion final de
-- la prueba.
testCasenewProofWE :: Relation -> Focus -> HoleInfo -> Proof -> Assertion
testCasenewProofWE r f hi res = let p = newProofWithoutEnd r f hi
                                     in unless (p == res) $
                                         assertFailure $ 
                                         "\n Resultado esperado: " ++ show res ++
                                         "\n Contra: " ++ show p

{- Agregamos un paso en el cual las prueba coinciden en su primer focus.

p_FxEqY:
    (F (x),Top)
Eq  {?}
    (y, Top)

p_FxEqZ:
    (F (x),Top)
Eq  {...}
    (z, Top)

Res:
    (F (x),Top)
Eq {...}
    (z,Top)
Eq {?}
    (y,Top)
-}
testCaseAddStep0 :: Assertion
testCaseAddStep0 = testCaseAddStep p_Fx_Eq_Y p_Fx_Eq_Z 
                   (Right $ Trans M.empty relEq f_Fx f_z f_y p_Fx_Eq_Z p_Z_Eq_Y)

{- Agregamos un paso en el cual las prueba coinciden en su ultimo y primer focus.
p_FxEqY:
    (F (x),Top)
Eq  {?}
    (y, Top)

p_YEqZ:
    (y,Top)
Eq  {...}
    (z, Top)

Res:
    (F (x),Top)
Eq {...}
    (y,Top)
Eq {?}
    (z,Top)
-}
testCaseAddStep1 :: Assertion
testCaseAddStep1 = testCaseAddStep p_Fx_Eq_Y p_Y_Eq_Z 
                   (Right $ Trans M.empty relEq f_Fx f_y f_z p_Fx_Eq_Y p_Y_Eq_Z)


{- Intentanmos agregar un paso en el que no coinciden las relaciones, luego
    entonces deberiamos devolver ClashRel.
p_FxEqY:
    (F (x),Top)
Eq  {?}
    (y, Top)

p_FxImplZ:
    (F (x),Top)
Impl  {...}
    (z, Top)

Res: ClashRelation eq impl
-}
testCaseAddStep2 :: Assertion
testCaseAddStep2 = testCaseAddStep p_Fx_Eq_Y p_Fx_Impl_Z 
                   (Left $ ClashRel relEq relImpl)

{- Intentamos agregar un paso en el que no coinciden los focus de las pruebas,
    luego entonces deberiamos devolver ClashAddStep.
p_FxEqY:
    (F (x),Top)
Eq  {?}
    (y, Top)

p_FyEqZ:
    (F (y),Top)
Impl  {...}
    (z, Top)

Res: ClashAddStep p_FxEqY p_FyEqZ
-}
testCaseAddStep3 :: Assertion
testCaseAddStep3 = testCaseAddStep p_Fx_Eq_Y p_Fy_Eq_Z 
                   (Left $ ClashAddStep p_Fx_Eq_Y p_Fy_Eq_Z)

-- Verifica los casos de test para, dada una prueba, agregar un paso, es decir
-- otra prueba y generar una nueva prueba por transitividad.
testCaseAddStep :: Proof -> Proof -> PM Proof -> Assertion
testCaseAddStep pf p res = let p' = addStep (toProofFocus pf) p
                           in unless (p' == res) $
                                assertFailure $ 
                                "\n Resultado esperado: " ++ show res ++
                                "\n Contra : " ++ show p

-- Conjunto de tests para pruebas.
testGroupProof :: Test
testGroupProof = testGroup "Proof" 
                 [ testGroup "*New proof"
                    [ testCase ("newProof Eq F(x) y => \n" ++
                                    "\t\t(F (x),Top) \n" ++
                                "\tEq  {?}\n" ++
                                    "\t\t(y, Top)")
                        testCaseNewProof0
                    , testCase ("newProof \" Partición de rango \" => \n" ++
                                "\t\t〈∀ x : R@x ∨ S@x : T@x〉\n" ++
                                "\tEquiv  {?}\n" ++
                                "\t\t〈∀ x : R@x : T@x〉 ∧ 〈∀ x : S@x : T@x〉")
                        testCaseNewProof1
                    , testCase ("newProof \" Teorema estrella \" => \n" ++
                                "\t\tp ∨ q\n" ++
                                "\tEquiv  {?}\n" ++
                                "\t\tp ∨ ¬q ≡ p")
                        testCaseNewProof2
                    ]
                 ,
                   testGroup "*New proof without end"
                    [ testCase ("newProofWithoutEnd \" Teorema estrella \" " ++
                                    "=> \n\t\tp ∨ q \n" ++
                                "\tEquiv  {?}\n" ++
                                    "\t\t?{p ∨ ¬q}")
                        testCasenewProofWE0
                    , testCase ("newProofWithoutEnd \" De morgan \" " ++
                                    "=> \n\t\t¬(p ∨ q) \n" ++
                                "\tEquiv  {?}\n" ++
                                    "\t\t?{}")
                        testCasenewProofWE1
                    ]
                 , testGroup "*Add step"
                    [ testCase ("addStep [(F (x),Top) Eq{?} (y, Top)]" ++
                                      " [(F (x),Top) Eq{...} (z, Top)] =>" ++
                                      "\n\t\t(F (x),Top)" ++
                                      "\n\tEq {...}" ++
                                      "\n\t\t(z,Top)" ++
                                      "\n\tEq {?}" ++
                                      "\n\t\t(y,Top)"
                                      )
                        testCaseAddStep0
                    , testCase ("addStep [(F (x),Top) Eq{?} (y, Top)]" ++
                                      " [(y,Top) Eq{...} (z, Top)] =>" ++
                                      "\n\t\t(F (x),Top)" ++
                                      "\n\tEq {...}" ++
                                      "\n\t\t(y,Top)" ++
                                      "\n\tEq {?}" ++
                                      "\n\t\t(z,Top)"
                                      )
                        testCaseAddStep1
                    , testCase ("addStep [(F (x),Top) Eq{?} (y, Top)]" ++
                                      " [(F (x),Top) Impl{...} (z, Top)] =>" ++
                                      "\n\t ClashRel Eq Impl"
                                      )
                        testCaseAddStep2
                    , testCase ("addStep [(F (x),Top) Eq{?} (y, Top)]" ++
                                      " [(F (y),Top) Eq{...} (z, Top)] =>" ++
                                      "\n\t ClashAddStep" ++
                                      " [(F (x),Top) Eq{?} (y, Top)]" ++
                                      " [(F (y),Top) Eq{...} (z, Top)]"
                                      )
                        testCaseAddStep3
                    ]
                 , testGroup "*Proof from truth"
                    [ testCase ("proofFromTruth [p ∧ q] [p ≡ q ≡ p ∨ q]" ++
                                      " Equiv goldenRule =>" ++
                                      "\n\t\t(p ∧ q, Top) " ++
                                      "\n\t Equiv {Ax \"Regla Dorada\":" ++
                                      " p ∧ q ≡ p ≡ q ≡ p ∨ q}" ++
                                      "\n\t\t(p ≡ q ≡ p ∨ q, Top)"
                                      )
                        testCaseProofFromAxiom0
                    , testCase ("proofFromTruth [p] [p ≡ True]" ++
                            " Equiv neutralEquiv =>" ++
                            "\n\t\t(p, Top) " ++
                            "\n\t Equiv {Ax \"Neutro de la equivalencia\":" ++
                            " p ≡ True ≡ p}" ++
                            "\n\t\t(True ≡ p, Top)"
                               )
                        testCaseProofFromAxiom1
                    ]
                 , testGroup "Serialización"
                    [testProperty "decode . encode == id" 
                        prop_serialization
                    ]
                 ]


{- Intento de añadir un paso en donde ninguna de las expresiones de los focus
    coincide;

p_FxEqY:
    (F (x),Top)
Eq  {?}
    (y, Top)

p_FyEqZ:
    (F (y),Top)
Impl  {...}
    (z, Top)

luego si añadimos un paso;
ClashAddStep p_FxEqY p_FyEqZ
-}
{-
p_FyEqZ = newProof relEq f_Fy f_z

p_ClashAddStep = addStep (toProofFocus p_FxEqY) p_FyEqZ-}
