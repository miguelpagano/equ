-- | Las PreExpresiones son árboles de expresiones no necesariamente
-- tipables con huecos. Como se comenta en el módulo Equ.Syntax, el
-- tipo que posiblemente puso el usuario está en las hojas del árbol.
module Equ.PreExpr where


import Equ.Syntax
{- Propiedades de PreExpresiones (QC): queremos poder respetar la forma
   de escribir una expresión.
   
    * 'pretty . parser = id'
    * 'parser . pretty = id'
-}

data PreExpr = Var Variable
             | Con Constant
             | Fun Func
             | Hole Hole
             | UnOp Operator PreExpr
             | BinOp Operator PreExpr PreExpr
             | App PreExpr PreExpr
             | Quant Quantifier Variable PreExpr PreExpr
             | Paren PreExpr

-- Los zippers pueden ser convenientes; la referencia es: ``The
-- Zipper'' de Gérard Huet en JFP. 

data Path = Top
          | UnOpD Operator Path
          | BinOpL Operator Path PreExpr
          | BinOpR Operator PreExpr Path
          | AppL Path PreExpr
          | AppR PreExpr Path
          | QuantL Quantifier Variable Path PreExpr
          | QuantR Quantifier Variable PreExpr Path 
          | ParenD Path

-- | Un Focus representa la expresión que consiste de completar el
-- hueco denotado por Path con la expresión PreExpr (eso es lo que
-- hace toExpr).
type Focus = (PreExpr,Path)

toExpr :: Focus -> PreExpr
toExpr (e,p) = undefined

toFocus :: PreExpr -> Focus
toFocus e = (e,Top)

toFocuses :: PreExpr -> [Focus]
toFocuses e = undefined

-- Propiedades (forall e):
--   forall t \in toFocuses e, toExpr t = e

-- Reemplaza la expresión enfocada por una nueva expresión.
replace :: Focus -> PreExpr -> Focus
replace (_,p) e' = (e',p)

-- Navegación dentro de un Zipper: TODO (ver el artículo).
goDown :: Focus -> Maybe Focus
goDown = undefined

goUp :: Focus -> Maybe Focus
goUp = undefined

goLeft :: Focus -> Maybe Focus
goLeft = undefined

goRight :: Focus -> Maybe Focus
goRight = undefined


