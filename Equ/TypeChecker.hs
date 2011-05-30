-- | Transforma una PreExpresión en una Expresión.
module Equ.TypeChecker where
import Equ.PreExpr
import Equ.Expr

{- 

   Las PreExpresiones y las Expresiones son básicamente árboles de
   sintaxis abstracta con distinta información en cada nodo.  Por
   ejemplo, podría ser que las PreExpresiones tengan un componente de
   tipo 'Maybe Type', mientras que el mismo componente en una Expresión
   será de tipo 'Type'. Esto nos permite ver las PreExpresiones cómo
   Expresiones parcialmente tipadas.

   Una cosa que sí necesitamos es información sobre por qué falló un
   chequeo/inferencia de tipos. 

   El type-checker usará en lo posible la información de tipos de las
   PreExpresiones; de esta manera podremos tener un chequeo incremental.

-}
