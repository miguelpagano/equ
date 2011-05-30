-- | Las PreExpresiones son árboles de expresiones no necesariamente
-- tipables con huecos.
module Equ.PreExpr where

{- Propiedades de PreExpresiones (QC): queremos poder respetar la forma
   de escribir una expresión.
   
    * 'pretty . parser = id'
    * 'parser . pretty = id'
-}