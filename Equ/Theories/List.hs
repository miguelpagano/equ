-- | El modulo de constructores de listas y sus s&#237;mbolos de
-- funci&#243;n.
{-# Language OverloadedStrings #-}
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
    -- ** Lista de axiomas de la teoria
    , theoryAxiomList
    -- * Versión tipada de operadores.
    , emptyList
    , append
    , concat
    , length
    , take
    , drop
    , index
    -- ** Concatenacion
    , emptyNeutralConcat
    , consConcat
    -- ** Cardinal
    , lengthEmptyList
    , lengthConsList
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
import Equ.PreExpr
import Equ.Rule
import Equ.Theories.AbsName
import Equ.Theories.Common

import Data.Text (Text)

import Equ.Theories.Arith (zero,successor)

-- | Constructor del tipo de listas polimorficas; el string indica el
-- nombre de la variable de tipo
tyListVar :: String -> Type
tyListVar = TyList . tyVar

-- | La lista vacia.
listEmpty :: Constant
listEmpty = Constant { conRepr = "[]"
                     , conName = Empty
                     , conTy = tyListVar "B"
                     }

-- | Extender la lista con un elemento por la izquierda.
listApp :: Operator
listApp = Operator { opRepr = "▹"
                   , opName = Append
                   , opTy = tyVar "A" :-> tyListVar "A" :-> tyListVar "A"
                   , opAssoc = ARight
                   , opNotationTy = NInfix
                   , opPrec = 12
                   }  

-- | Tomar el n-esimo elemento de la lista.
listIndex :: Operator
listIndex = Operator { opRepr = "."
                     , opName = Index
                     , opTy = tyListVar "A" :-> TyAtom ATyNat :-> tyVar "A"
                     , opAssoc = ALeft
                     , opNotationTy = NInfix
                     , opPrec = 11
                     }
-- | Concatenacion de listas.                     
listConcat :: Operator
listConcat = Operator { opRepr = "++"
                      , opName = Concat
                      , opTy = tyListVar "A" :-> tyListVar "A" :-> tyListVar "A"
                      , opAssoc = ALeft
                      , opNotationTy = NInfix
                      , opPrec = 10
                      }

-- | Cardinal de la lista.
listLength :: Operator
listLength = Operator { opRepr = "#"
                    , opName = Length
                    , opTy = tyListVar "A" :-> TyAtom ATyNat
                    , opAssoc = None
                    , opNotationTy = NPrefix
                    , opPrec = 10
                    }

-- | Toma los primeros n elementos de una lista.
listTake :: Operator
listTake = Operator { opRepr = "↑"
                    , opName = Take
                    , opTy = tyListVar "A" :-> TyAtom ATyNat :-> tyListVar "A"
                    , opAssoc = ALeft
                    , opNotationTy = NInfix
                    , opPrec = 10
                    }

-- | Tira los primeros n elementos de una lista.
listDrop :: Operator
listDrop = Operator { opRepr = "↓"
                    , opName = Drop
                    , opTy = tyListVar "A" :-> TyAtom ATyNat :-> tyListVar "A"
                    , opAssoc = ALeft
                    , opNotationTy = NInfix
                    , opPrec = 10
                    }

-- | Constantes de listas.
theoryConstantsList :: [Constant]
theoryConstantsList = [listEmpty]
-- | Operadores de listas.
theoryOperatorsList :: [Operator]
theoryOperatorsList = [listApp,listConcat,listDrop,listIndex,listLength,listTake]
-- | Quantificadores de listas.
theoryQuantifiersList :: [Quantifier]
theoryQuantifiersList = []

-- | Constructor de variable de tipo lista polimorfica; el primer string es
-- el nombre de la variable, el segundo el nombre de la variable de tipo
varList :: Text -> String -> Expr
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

{- | Caso base:

@
    [] ++ ys = ys
@

-}
emptyNeutralConcat :: (Text,Expr)
emptyNeutralConcat = ( "Neutro a izquierda de concatenación" 
                     , leftNeutral concat emptyList varYS
                     )
    where varYS = varList "ys" "A"

{- | Caso inductivo

@
    (x &#9657; xs) ++ ys = x &#9657; (xs ++ ys)
@

-}
consConcat :: (Text, Expr)
consConcat = ( "Concatenar lista no vacía",
              ((varX `append` varXS) `concat` varYS) `equal` 
              (varX `append` (varXS `concat` varYS))
            )
    where varX = Expr $ Var $ var "x" $ tyVar "A"
          varXS = varList "xs" "A"
          varYS = varList "ys" "A"


-- Reglas para la definicion de length (#)

{- | Caso base:

@
    #[] = 0
@

-}
lengthEmptyList :: (Text,Expr)
lengthEmptyList = ( "Longitud de la lista vacía"
                  , (length emptyList) `equal` zero
                  )
{- | Caso inductivo de la longitud de una lista.

@
    \# (x &#9657; xs) = 1 + # xs
@

-}
lengthConsList :: (Text,Expr)
lengthConsList = ( "Longitud de lista no vacía"
                 , (length (append varX varXS)) `equal` 
                   (successor $ length varXS)
                 )
    where varX = Expr $ Var $ var "x" $ tyVar "A"
          varXS = varList "xs" "A"

-- NOTA: En el libro Calculo de Programas, se incluyen otras reglas
-- para la definicion de length con respecto a las operaciones concat,
-- take y drop. Se opt&#243; por incluir solo las que involucran
-- constructores, las demas pueden derivarse.


-- Reglas para la definicion de take.

{- | Caso base 1 de tomar:

@
    xs &#8593; 0 = []
@

-}
zeroTake :: (Text,Expr) 
zeroTake = ( "Tomar cero elementos"
           , (take varXS zero) `equal` emptyList
           )
    where varXS = varList "xs" "A"
                      
{- | Caso base 2 de tomar:

@
    [] &#8593; n = []
@

-}
emptyTake :: (Text,Expr)
emptyTake = ( "Tomar de la lista vacía"
            , (take emptyList varN) `equal`  emptyList
            )
    where varN = Expr $ Var $ var "x" $ TyAtom ATyNat

{- | Caso inductivo de tomar:

@
    (x &#9657; xs) &#8593; (n+1) = x &#9657; (xs &#8593; n)
@

-}
consTake :: (Text,Expr)
consTake = ( "Tomar (n+1) elementos"
           , (take (append varX varXS) (successor varN)) `equal`
             (append varX $ take varXS varN)
           )
    where varXS = varList "xs" "A"
          varX = Expr $ Var $ var "x" $ tyVar "A"
          varN = Expr $ Var $ var "n" $ TyAtom ATyNat
          

-- Reglas para la definicion de drop

{- | Caso base 1 de tirar:

@
    xs &#8595; 0 = xs
@

-}
zeroDrop :: (Text,Expr)
zeroDrop = ( "Tirar cero elementos"
           , drop varXS zero `equal` varXS
           )
    where varXS = varList "xs" "A"

{- | Caso base 2 de tirar:

@
    [] &#8595; n = []
@

-}
emptyDrop :: (Text,Expr)
emptyDrop = ( "Tirar de la lista vacía"
            , (drop emptyList varN) `equal` emptyList
            )
    where varN = Expr $ Var $ var "x" $ TyAtom ATyNat

{- | Caso inductivo de tirar.

@
    (x &#9657; xs) &#8595; (n+1) = xs &#8595; n
@

-}
consDrop :: (Text,Expr)
consDrop = ( "Tirar (n+1) elementos"
           , (drop (append varX varXS) (successor varN)) `equal`
             (drop varXS varN)
           )
    where varXS = varList "xs" "A"
          varX = Expr $ Var $ var "x" $ tyVar "A"
          varN = Expr $ Var $ var "n" $ TyAtom ATyNat
          
-- Reglas para la definicion de Index

{- | Caso base de la proyeccion:

@
   (x &#9657; xs).0 = x
@

-}
zeroIndex :: (Text,Expr)
zeroIndex = ( "Proyectar el elemento inicial" 
            , (index (append varX varXS) zero) `equal` varX
            )
    where varXS = varList "xs" "A"
          varX = Expr $ Var $ var "x" $ tyVar "A"

{- | Caso inductivo de la proyeccion:

@
   (x &#9657; xs).(n+1) = xs.n
@

-}
consIndex :: (Text,Expr)
consIndex = ( "Proyectar el elemento (i+1)"
            , (index (append varX varXS) (successor varN)) `equal`
              (index varXS varN)
            )
    where varXS = varList "xs" "A"
          varX = Expr $ Var $ var "x" $ tyVar "A"
          varN = Expr $ Var $ var "n" $ TyAtom ATyNat

theoryAxiomList :: [(Text,Expr)]
theoryAxiomList = [ emptyNeutralConcat
                  , consConcat
                  -- ** Cardinal
                  , lengthEmptyList
                  , lengthConsList
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
                  ]