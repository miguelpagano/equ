-- | Declaración de nombres de constantes, operadores y cuantificadores.
-- Esta definición es para tener un mecanismo eficiente de pattern matching
module Equ.Theories.AbsName where

import Test.QuickCheck(Arbitrary, arbitrary, elements)

-- | Nombres de constantes
data ConName = Empty  -- ^ Lista: vacia
               | Zero -- ^ Num (polimorfico): cero
               | CTrue -- ^ FOL: true
               | CFalse -- ^ FOL: false
                 deriving (Eq,Ord)

-- | Nombres de operadores
data OpName = Append    -- ^ Lista: agregar por la izquierda 
              | Index   -- ^ Lista: indexar
              | Length  -- ^ Lista: longitud
              | Concat  -- ^ Lista: concatenar
              | Take    -- ^ Lista: tomar una cantidad de elementos
              | Drop    -- ^ Lista: tirar una cantidad de elementos
              | Succ    -- ^ Num (polimorfico): sucesor
              | Sum     -- ^ Num (polimorfico): suma
              | Prod    -- ^ Num (polimorfico): producto
              | Equival   -- ^ FOL: Equivalencia
              | Discrep -- ^ FOL: Discrepancia
              | Implic    -- ^ FOL: Implicacion
              | Conseq  -- ^ FOL: Consecuencia
              | And     -- ^ FOL: "y" lógico
              | Or      -- ^ FOL: "o" lógico
              | Neg     -- ^ FOL: Negación
                 deriving (Eq,Ord)

              
-- | Nombres de cuantificadores
data QuantName = Forall  -- ^ FOL: para todo
               | Exist -- ^ FOL: existe
                 deriving (Eq,Ord)

-- | Instancia arbitrary para ConName
instance Arbitrary ConName where
    arbitrary = elements [Empty, Zero, CTrue, CFalse]

-- | Instancia arbitrary para OpName
instance Arbitrary OpName where 
    arbitrary = 
        elements [  Append
                    , Index
                    , Length
                    , Concat  
                    , Take
                    , Drop
                    , Succ
                    , Sum
                    , Equival
                    , Discrep
                    , Implic
                    , Conseq
                    , And
                    , Or
                    , Neg
                    ]

-- | Instancia arbitrary para QuantName
instance Arbitrary QuantName where
    arbitrary = elements [Forall, Exist]
