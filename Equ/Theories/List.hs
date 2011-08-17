-- | El modulo de constructores de listas y sus símbolos de
-- función.

module Equ.Theories.List 
    ( -- * Constructores y operadores.
      listEmpty
    , listApp 
    , listIndex
    , listConcat
    , listLength
    , listTake
    , listDrop
    -- ** Listas de constructores y operadores
    , theoryConstantsList
    , theoryOperatorsList
    , theoryQuantifiersList
    -- * Versión tipada de operadores.
    , emptyList
    , append
    , concat
    , length
    , take
    , drop
    , index
    -- * Reglas de la teoría.
    , listRules
    -- ** Concatenacion
    , emptyConcat
    , consConcat
    -- ** Cardinal
    , emptyLength
    , consLength
    -- ** Tomar n elementos
    , zeroTake
    , emptyTake
    , consTake
    -- ** Tirar n elementos
    , zeroDrop
    , emptyDrop
    , consDrop
    -- ** Proyeccion n-esimo elemento
    , zeroIndex
    , consIndex
    )
    where
    
import Prelude hiding (concat,take,drop,length,sum)
import Equ.Syntax
import Equ.Types
import Equ.Expr
import Equ.PreExpr.Internal
import Equ.Rule
import Equ.Theories.AbsName

import Data.Text (pack)

import Equ.Theories.Arith (zero,successor)

-- | Constructor del tipo de listas polimorficas; el string indica el
-- nombre de la variable de tipo
tyListVar :: String -> Type
tyListVar = TyList . tyVar

-- | La lista vacia.
listEmpty :: Constant
listEmpty = Constant { conRepr = pack "[]"
                     , conName = Empty
                     , conTy = tyListVar "B"
                     }

-- | Extender la lista con un elemento por la izquierda.
listApp :: Operator
listApp = Operator { opRepr = pack "▹"
                   , opName = Append
                   , opTy = tyVar "A" :-> tyListVar "A" :-> tyListVar "A"
                   , opAssoc = ARight
                   , opNotationTy = NInfix
                   , opPrec = 12
                   }  

-- | Tomar el n-esimo elemento de la lista.
listIndex :: Operator
listIndex = Operator { opRepr = pack "."
                     , opName = Index
                     , opTy = tyListVar "A" :-> TyAtom ATyNat :-> tyVar "A"
                     , opAssoc = ALeft
                     , opNotationTy = NInfix
                     , opPrec = 11
                     }
-- | Concatenacion de listas.                     
listConcat :: Operator
listConcat = Operator { opRepr = pack "++"
                      , opName = Concat
                      , opTy = tyListVar "A" :-> tyListVar "A" :-> tyListVar "A"
                      , opAssoc = ALeft
                      , opNotationTy = NInfix
                      , opPrec = 10
                      }

-- | Cardinal de la lista.
listLength :: Operator
listLength = Operator { opRepr = pack "#"
                    , opName = Length
                    , opTy = tyListVar "A" :-> TyAtom ATyNat
                    , opAssoc = None
                    , opNotationTy = NPrefix
                    , opPrec = 10
                    }

-- | Toma los primeros n elementos de una lista.
listTake :: Operator
listTake = Operator { opRepr = pack "↑"
                    , opName = Take
                    , opTy = tyListVar "A" :-> TyAtom ATyNat :-> tyListVar "A"
                    , opAssoc = ALeft
                    , opNotationTy = NInfix
                    , opPrec = 10
                    }

-- | Tira los primeros n elementos de una lista.
listDrop :: Operator
listDrop = Operator { opRepr = pack "↓"
                    , opName = Drop
                    , opTy = tyListVar "A" :-> TyAtom ATyNat :-> tyListVar "A"
                    , opAssoc = ALeft
                    , opNotationTy = NInfix
                    , opPrec = 10
                    }

theoryConstantsList :: [Constant]
theoryConstantsList = [listEmpty]
theoryOperatorsList :: [Operator]
theoryOperatorsList = [listApp,listConcat,listDrop,listIndex,listLength,listTake]
theoryQuantifiersList :: [Quantifier]
theoryQuantifiersList = []

-- | Constructor de variable de tipo lista polimorfica; el primer string es
-- el nombre de la variable, el segundo el nombre de la variable de tipo
varList :: String -> String -> Expr
varList s t = Expr $ Var $ listVar s t
    where listVar v ty = var v $ tyListVar ty

-- | Constructor de lista vacia
emptyList :: Expr
emptyList = Expr $ Con $ listEmpty

-- | Constructor de insercion por izquierda
-- PRE: Las expresiones son del tipo adecuado
append :: Expr -> Expr -> Expr
append (Expr x) (Expr xs) = Expr $ BinOp listApp x xs

-- | Constructor de concatenacion
concat :: Expr -> Expr -> Expr
concat (Expr xs) (Expr ys) = Expr $ BinOp listConcat xs ys

-- | Constructor de length
length :: Expr -> Expr
length (Expr xs) = Expr $ UnOp listLength xs

-- | Constructor de take
take :: Expr -> Expr -> Expr
take (Expr xs) (Expr n) = Expr $ BinOp listTake xs n

-- | Constructor de drop
drop :: Expr -> Expr -> Expr
drop (Expr xs) (Expr n) = Expr $ BinOp listDrop xs n

-- | Constructor de index
index :: Expr -> Expr -> Expr
index (Expr xs) (Expr n) = Expr $ BinOp listIndex xs n


-- Reglas para la definicion de Concatenar (++)

-- Caso base:
-- [] ++ ys = ys
emptyConcat :: Rule
emptyConcat = Rule { lhs = concat emptyList varYS
                   , rhs = varYS
                   , rel = relEq
                   , name = pack "concatenacion-vacia"
                   , desc = pack ""
                   }
    where varYS = varList "ys" "A"

-- Caso inductivo
-- (x ▹ xs) ++ ys = x ▹ (xs ++ ys)
consConcat :: Rule
consConcat = Rule { lhs = concat (append varX varXS) varYS
                  , rhs = append varX (concat varXS varYS)
                  , rel = relEq
                  , name = pack "concatenacion-cons"
                  , desc = pack ""
                  }
    where varX = Expr $ Var $ var "x" $ tyVar "A"
          varXS = varList "xs" "A"
          varYS = varList "ys" "A"


-- Reglas para la definicion de length (#)

-- Caso base:
-- #[] = 0
emptyLength :: Rule
emptyLength = Rule { lhs = length emptyList
                   , rhs = zero
                   , rel = relEq
                   , name = pack "longitud-vacia"
                   , desc = pack ""
                   }

-- Caso inductivo
-- # (x ▹ xs) = 1 + # xs
consLength :: Rule
consLength = Rule { lhs = length (append varX varXS)
                  , rhs = successor $ length varXS
                  , rel = relEq
                  , name = pack "longitud-cons"
                  , desc = pack ""
                  }
    where varX = Expr $ Var $ var "x" $ tyVar "A"
          varXS = varList "xs" "A"

-- NOTA: En el libro Calculo de Programas, se incluyen otras reglas para la definicion de length
--       con respecto a las operaciones concat, take y drop. Se optó por incluir solo las que involucran
--       constructores, las demas pueden derivarse.


-- Reglas para la definicion de take

-- Caso base 1:
-- xs ↑ 0 = []
zeroTake :: Rule
zeroTake = Rule { lhs = take varXS zero
                , rhs = emptyList
                , rel = relEq
                , name = pack "tomar-cero"
                , desc = pack ""
                }
    where varXS = varList "xs" "A"
                      
-- Caso base 2:
-- [] ↑ n = []
emptyTake :: Rule
emptyTake = Rule { lhs = take emptyList varN
                 , rhs = emptyList
                 , rel = relEq
                 , name = pack "tomar-vacia"
                 , desc = pack ""
                 }
    where varN = Expr $ Var $ var "x" $ TyAtom ATyNat

-- Caso inductivo:
-- (x ▹ xs) ↑ (n+1) = x ▹ (xs ↑ n)
consTake :: Rule
consTake = Rule { lhs = take (append varX varXS) (successor varN)
                , rhs = append varX $ take varXS varN 
                , rel = relEq
                , name = pack "tomar-inductivo"
                , desc = pack ""
                }
    where varXS = varList "xs" "A"
          varX = Expr $ Var $ var "x" $ tyVar "A"
          varN = Expr $ Var $ var "n" $ TyAtom ATyNat
          

-- Reglas para la definicion de drop

-- Caso base 1:
-- xs ↓ 0 = xs
zeroDrop :: Rule
zeroDrop = Rule { lhs = drop varXS zero
                , rhs = varXS
                , rel = relEq
                , name = pack "tirar-cero"
                , desc = pack ""
                }
    where varXS = varList "xs" "A"

-- Caso base 2:
-- [] ↓ n = []
emptyDrop :: Rule
emptyDrop = Rule { lhs = drop emptyList varN
                 , rhs = emptyList
                 , rel = relEq
                 , name = pack "tirar-vacia"
                 , desc = pack ""
                 }
    where varN = Expr $ Var $ var "x" $ TyAtom ATyNat

-- Caso inductivo
-- (x ▹ xs) ↓ (n+1) = xs ↓ n
consDrop :: Rule
consDrop = Rule { lhs = drop (append varX varXS) (successor varN)
                , rhs = drop varXS varN
                , rel = relEq
                , name = pack "tirar-inductivo"
                , desc = pack ""
                }
    where varXS = varList "xs" "A"
          varX = Expr $ Var $ var "x" $ tyVar "A"
          varN = Expr $ Var $ var "n" $ TyAtom ATyNat
          
-- Reglas para la definicion de Index

{- | Caso base de la proyeccion:
@
   (x ▹ xs).0 = x
@
 -}
zeroIndex :: Rule
zeroIndex = Rule { lhs = index (append varX varXS) zero
                 , rhs = varX
                 , rel = relEq
                 , name = pack "indizar-cero"
                 , desc = pack ""
                 }
    where varXS = varList "xs" "A"
          varX = Expr $ Var $ var "x" $ tyVar "A"

{- | Caso inductivo de la proyeccion:
@
   (x ▹ xs).(n+1) = xs.n
@
-}
consIndex :: Rule
consIndex = Rule { lhs = index (append varX varXS) (successor varN)
                 , rhs = index varXS varN
                 , rel = relEq
                 , name = pack "indizar-ind"
                 , desc = pack ""
                 }
    where varXS = varList "xs" "A"
          varX = Expr $ Var $ var "x" $ tyVar "A"
          varN = Expr $ Var $ var "n" $ TyAtom ATyNat

-- NOTA: No hay reglas para lista vacia en la operacion index.
listRules :: [Rule]
listRules = [ emptyConcat
            , consConcat
            , emptyLength
            , consLength
            , zeroTake
            , emptyTake
            , consTake
            , zeroDrop
            , emptyDrop
            , consDrop
            , zeroIndex
            , consIndex
            ]
