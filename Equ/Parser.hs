-- | Este modulo es el parser a Pre-Expresiones. 
module Equ.Parser where

import Equ.PreExpr 
import Equ.Types
import Data.Text

-- | Este tipo representa todos los posibles errores de parseo.
-- TODO: Extender según la necesidad; recordar guardar la información
-- sobre posiciones del error.
data ParseError = ParseError

-- | Obviamente, la función principal de este módulo. Probablemente
-- necesitemos una función más general que tenga en cuenta el contexto
-- en el que queremos parsear algo para de esa manera poder dar
-- errores informativos.
parser :: Text -> Either ParseError PreExpr
parser = undefined

-- | Para definir la función anterior podemos necesitar definir 
-- esta función para poder parsear los tipos que el usuario quiera
-- asignar a los diferentes constituyentes de pre-expresiones.
parserTy :: Text -> Either ParseError Type
parserTy = undefined