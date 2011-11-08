{-# Language OverloadedStrings #-}
module TestSuite.Tests.Parser where

import Equ.Types
import Equ.Parser
import Equ.Syntax
import Equ.PreExpr
import Equ.Theories.FOL hiding (true, false)
import Equ.Theories.List
import Equ.Theories.Arith

import Test.HUnit (Assertion, assertFailure)
import Test.Framework (testGroup, Test)
import Test.Framework.Providers.HUnit (testCase)

import Data.Text
import Control.Monad (unless)

-- Variables para utilizar para los test de parseo.
p :: Variable
p = Variable { varName = pack "p"
             , varTy = TyUnknown
             }

q :: Variable
q = Variable { varName = pack "q"
             , varTy = TyUnknown
             }

x :: Variable
x = Variable { varName = pack "x"
             , varTy = TyUnknown
             }

w :: Variable
w = Variable { varName = pack "w"
             , varTy = TyUnknown
             }

z :: Variable
z = Variable { varName = pack "z"
              , varTy = TyUnknown
              }

ys :: Variable
ys = Variable { varName = pack "ys"
              , varTy = TyUnknown
              }
              
s :: Func
s = Func { funcName = pack "S"
         , funcTy = tyVar "VInt0"
         }

-- Variables a utilizar para los demas casos de tests.
v0 :: Variable
v0 = var "v0" TyUnknown
y :: Variable
y = var "y" TyUnknown

-- True
true :: PreExpr
true = Con $ folTrue

-- False
false :: PreExpr
false = Con $ folFalse

-- p v p
pVp :: PreExpr
pVp = BinOp folOr (Var p) (Var p)

-- p v q
pVq :: PreExpr
pVq = BinOp folOr (Var p) (Var q)

-- True v False
trueVfalse :: PreExpr
trueVfalse = BinOp folOr true false

-- S@y
sAppy :: PreExpr
sAppy = App (Fun s) (Var y)

-- S@0
sApp0 :: PreExpr
sApp0 = App (Fun s) (Con natZero)

-- (x+S@0)
xPlussApp0 :: PreExpr
xPlussApp0 = Paren $ (BinOp natSum (Var x) sApp0)

-- S@(x+S@0)
sApp1 :: PreExpr
sApp1 = App (Fun s) xPlussApp0

-- x + S@y + z
xPlusSyPlusZ :: PreExpr
xPlusSyPlusZ = BinOp natSum (BinOp natSum (Var x) sAppy) (Var z)

-- S@y + S@(x+S@0) + z
sAppyPlusSomePlusz :: PreExpr
sAppyPlusSomePlusz = BinOp natSum (BinOp natSum sAppy sApp1) (Var z)

-- [x]
listX :: PreExpr
listX = BinOp listApp (Var x) (Con listEmpty)

-- [y,w]
listYW :: PreExpr
listYW = BinOp listApp (Var y) $ BinOp listApp (Var w) (Con listEmpty)

-- [x] ++ [y,w]
listXConcatListYW :: PreExpr
listXConcatListYW = BinOp listConcat listX listYW

-- #([x] ++ [y,w]) 
lengthList :: PreExpr
lengthList = UnOp listLength $ Paren listXConcatListYW

-- #([x] ++ [y,w]) + z
lengthListPlusz :: PreExpr
lengthListPlusz = BinOp natSum lengthList (Var z)

testParse0 :: Assertion
testParse0 = testParse s $ Var p
    where s = "p"

testParse1 :: Assertion
testParse1 = testParse s $ Var ys
    where s = "ys"

testParse2 :: Assertion
testParse2 = testParse s $ sApp0
    where s = "S@0"
          
testParse3 :: Assertion
testParse3 = testParse s $ sAppy
    where s = "S@y"
          
testParse4 :: Assertion
testParse4 = testParse s $ xPlussApp0
    where s = "(x+S@0)"

testParse5 :: Assertion
testParse5 = testParse s $ xPlusSyPlusZ
    where s = "x + S@y + z"
          
testParse6 :: Assertion
testParse6 = testParse s $ sAppyPlusSomePlusz
    where s = "S@y + S@(x+S@0) + z"

testParse7 :: Assertion
testParse7 = testParse s $ listX
    where s = "[x]"

testParse8 :: Assertion
testParse8 = testParse s $ listYW
    where s = "[y,w]"

testParse9 :: Assertion
testParse9 = testParse s $ listXConcatListYW
    where s = "[x] ++ [y,w]"

testParse10 :: Assertion
testParse10 = testParse s $ lengthList
    where s = "#([x] ++ [y,w])"

-- TODO: Este es un caso en el que falla el parser. Para mas info del error
-- es interesante hacer goDown de la expresión esperada contra la expresión
-- parseada.
testParse11 :: Assertion
testParse11 = testParse s $ lengthListPlusz
    where s = "#([x] ++ [y,w]) + z"

-- Controlamos que el parseo de un string sea el esperado, comparandolo con
-- la preExpresion que le pasamos. TODO: Sobre el control de errores,
-- ParseError no tiene instancia de Eq, esto genera un problema para comparar.
-- Por esa razon de momento no testeamos errores informativos de parseo.
testParse :: String -> PreExpr -> Assertion
testParse s pe = let Right pe' = parseFromString s
                       in unless (pe == pe') $
                            assertFailure $ 
                            "\n Resultado esperado: " ++ show pe ++
                            "\n Contra : " ++ show pe'

testGroupParse :: Test
testGroupParse = testGroup "Parser" 
                 [ testCase "Parser \"p\""
                    testParse0
                 , testCase "Parser \"ys\""
                    testParse1
                 , testCase "Parser \"S@0\""
                    testParse2
                 , testCase "Parser \"S@y\""
                    testParse3
                 , testCase "Parser \"(x+S@0)\""
                    testParse4
                 , testCase "Parser \"x + S@y + z\""
                    testParse5
                 , testCase "Parser \"S@y + S@(x+S@0) + z\""
                    testParse6
                 , testCase "Parser \"[x]\""
                    testParse7
                 , testCase "Parser \"[y,w]\""
                    testParse8
                 , testCase "Parser \"[x] ++ [y,w]\""
                    testParse9
                 , testCase "Parser \"#([x] ++ [y,w])\""
                    testParse10
                 , testCase "Parser \"#([x] ++ [y,w]) + z\""
                    testParse11
                 ]
