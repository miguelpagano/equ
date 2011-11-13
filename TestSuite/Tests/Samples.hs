{-# Language OverloadedStrings #-}

module TestSuite.Tests.Samples where

import Equ.Types
import Equ.Parser
import Equ.Syntax
import Equ.PreExpr
import Equ.Theories.FOL hiding (true, false)
import Equ.Theories.List
import Equ.Theories.Arith
import Data.Text (pack)

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
              
varS :: Func
varS = Func { funcName = pack "S"
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
sAppy = App (Fun varS) (Var y)

-- S@0
sApp0 :: PreExpr
sApp0 = App (Fun varS) (Con natZero)

-- (x+S@0)
xPlussApp0 :: PreExpr
xPlussApp0 = Paren $ (BinOp natSum (Var x) sApp0)

-- S@(x+S@0)
sApp1 :: PreExpr
sApp1 = App (Fun varS) xPlussApp0

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
