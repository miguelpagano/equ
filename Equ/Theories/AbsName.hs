-- | Declaración de nombres de constantes, operadores y cuantificadores.
-- Esta definición es para tener un mecanismo eficiente de pattern matching
module Equ.Theories.AbsName where
    
-- | Nombres de constantes
data ConName = Empty  -- ^ Lista: vacia
               | Zero -- ^ Num (polimorfico): cero
               
-- | Nombres de operadores
data OpName = Append    -- ^ Lista: agregar por la izquierda 
              | Index   -- ^ Lista: indexar
              | Length  -- ^ Lista: longitud
              | Concat  -- ^ Lista: concatenar
              | Take    -- ^ Lista: tomar una cantidad de elementos
              | Drop    -- ^ Lista: tirar una cantidad de elementos
              | Succ    -- ^ Num (polimorfico): sucesor
              | Sum     -- ^ Num (polimorfico): suma
              
-- | Nombres de cuantificadores
data QuantName = Forall  -- ^ FOL: para todo
                 | Exist -- ^ FOL: existe