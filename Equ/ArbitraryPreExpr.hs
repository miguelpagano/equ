import Equ.Syntax
import Equ.Types
import Equ.PreExpr
import Data.Text
import Test.QuickCheck
import Test.QuickCheck.Gen
import System.Random
import Control.Monad

-- Instancia arbitrary para text, en principio no la usamos; 
-- generaba demasiada aleatoriedad de preExpr y no servia de mucho.
-- Generaba por ejemplo cosas como (+)(Forall) in (and) | ((ForSome) + (A))
instance Arbitrary Text where
    arbitrary = 
        oneof [ return (pack "ForAll")
                , return (pack "ForSome")
                , return (pack "+")
                , return (pack "-")
                , return (pack "*")
                , return (pack "/")
                , return (pack "and")
                , return (pack "or")
                , return (pack "implies")
                , return (pack "iff")
                ]

-- Instancia arbitrary para los tipos atómicos.
instance Arbitrary AtomTy where
    arbitrary = elements [ATyNum, ATyInt, ATyNat, ATyBool]
    
-- Instancia arbitrary para los tipos generales.
instance Arbitrary Type where
    arbitrary = 
        oneof [ return TyUnknown
                , liftM TyVar arbitrary
                , liftM TyList arbitrary
                , liftM TyAtom arbitrary
                , liftM2 (:->) arbitrary arbitrary
                ]

-- Instancia arbitrary para las variables, acá es donde usaríamos la instancia
-- arbitraty de Text pero en su lugar nos concentramos en un conjunto reducido
-- pero mucho mas útil de indicadores de variable.
instance Arbitrary Variable where
    arbitrary = 
        oneof [ liftM (Variable $ pack "X") arbitrary
                , liftM (Variable $ pack "Y") arbitrary
                , liftM (Variable $ pack "Z") arbitrary
                , liftM (Variable $ pack "W") arbitrary
                , liftM (Variable $ pack "V") arbitrary
                , liftM (Variable $ pack "U") arbitrary
                ]

-- Instancia arbitrary para constantes, casi análogo a las variables.
instance Arbitrary Constant where
    arbitrary = 
        oneof [ liftM (Constant $ pack "A") arbitrary
                , liftM (Constant $ pack "B") arbitrary
                , liftM (Constant $ pack "C") arbitrary
                , liftM (Constant $ pack "D") arbitrary
                , liftM (Constant $ pack "E") arbitrary
                , liftM (Constant $ pack "F") arbitrary
                , liftM (Constant $ pack "G") arbitrary
                ]

-- Instancia arbitrary para los operadores binarios, en realidad no necesariamente
-- un operador pertenece a los binarios, pero de nuevo por prolijidad a la hora 
-- de la lectura los usamos como binarios.
instance Arbitrary Operator where
    arbitrary = 
        oneof [ liftM (Operator $ pack "+") arbitrary
                , liftM (Operator $ pack "-") arbitrary
                , liftM (Operator $ pack "/") arbitrary
                , liftM (Operator $ pack "*") arbitrary
                , liftM (Operator $ pack "and") arbitrary
                , liftM (Operator $ pack "or") arbitrary
                , liftM (Operator $ pack "implies") arbitrary
                , liftM (Operator $ pack "iff") arbitrary
                ]

-- Instancia arbitrary para las funciones, análogo los casos anteriores.
instance Arbitrary Func where
    arbitrary = 
        oneof [ liftM (Func $ pack "F") arbitrary
                , liftM (Func $ pack "G") arbitrary
                , liftM (Func $ pack "H") arbitrary
                , liftM (Func $ pack "Lam") arbitrary
                ]

-- Instancia arbitrary para los cuantificadores, acá en principio la única 
-- restricción importante es que un cuantificador empieza con ForAll o ForSome.
instance Arbitrary Quantifier where
    arbitrary = 
        oneof [ liftM (Quantifier $ pack "ForAll") arbitrary
                , liftM (Quantifier $ pack "ForSome") arbitrary
                ]

-- Instancia arbitrary para los huecos.
instance Arbitrary Hole where
    arbitrary = liftM Hole arbitrary

-- Instancia arbitrary para las preExpresiones, lo único que dejamos fijo es el 
-- operador unario, esto para simplificar la forma de las preExpresiones.
instance Arbitrary PreExpr where
    arbitrary =
        oneof [ liftM  Var arbitrary
                , liftM Con arbitrary
                , liftM Fun arbitrary
                , liftM PrExHole arbitrary
                , liftM (UnOp op) arbitrary
                , liftM3 BinOp arbitrary arbitrary arbitrary
                , liftM2 App arbitrary arbitrary
                , liftM4 Quant arbitrary arbitrary arbitrary arbitrary
                , liftM Paren arbitrary
                ]
                
-- Operador - unario para el caso respectivo en Arbitrary PreExpr.
op = Operator (pack "-") TyUnknown

-- Auxiliar que usamos para devolver una lista aleatoria de preExpresiones.
giveMePreExpAux :: Int -> Int -> [PreExpr]
giveMePreExpAux n m = let l = unGen arbitrary (mkStdGen m) m :: [PreExpr]
                        in
                            if Prelude.length l < n
                                then giveMePreExpAux n (m+1)
                                else l

-- Dado un n retorna una lista de preExpresiones tal que #[PreExpr] >=n
giveMePreExp :: Int -> [PreExpr]
giveMePreExp n = giveMePreExpAux n 0

-- Checkea que (forall e):
--   forall t \in toFocuses e, toExpr t = e
prop_toFocuses :: PreExpr -> Bool
prop_toFocuses preExp = prop_toFocusesAux preExp (toFocuses preExp)

-- Auxiliar para checkear la propiedad de arriba.
prop_toFocusesAux :: PreExpr -> [Focus] -> Bool
prop_toFocusesAux preExp [] = True
prop_toFocusesAux preExp (x:xs) | toExpr x == preExp = prop_toFocusesAux preExp xs
                                | otherwise = False
