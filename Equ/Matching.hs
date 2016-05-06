{-| Algoritmo de matching entre expresiones. La función principal de
este módulo toma dos expresiones @ptn@ y @expr@ e intenta generar la
substitución de las variables que aparecen en @ptn@ de manera que al
aplicarla sobre @ptn@ se obtenga expr.  Este es un algoritmo bien
conocido. La unica variacion es que contamos con expresiones
cuantificadas; en esas expresiones, las variables cuantificadas son
tratadas como parámetros.  -}

module Equ.Matching
    ( module Equ.Matching.Error
    , match
    , VariableRename
    )
    where

import Equ.Matching.Error
import Equ.Matching.Matching



