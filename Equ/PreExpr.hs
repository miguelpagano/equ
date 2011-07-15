-- | Las PreExpresiones son árboles de expresiones no necesariamente
-- tipables con huecos. Como se comenta en el módulo Equ.Syntax, el
-- tipo que posiblemente puso el usuario está en las hojas del árbol.
module Equ.PreExpr where


import Equ.Syntax
import Data.Text

{- Propiedades de PreExpresiones (QC): queremos poder respetar la forma
   de escribir una expresión.
   
    * 'pretty . parser = id'
    * 'parser . pretty = id'
-}

data PreExpr = Var Variable
             | Con Constant
             | Fun Func
             | PrExHole Hole
             | UnOp Operator PreExpr
             | BinOp Operator PreExpr PreExpr
             | App PreExpr PreExpr
             | Quant Quantifier Variable PreExpr PreExpr
             | Paren PreExpr
            deriving (Eq)

-- | Pretty print para las preExpresiones.
instance Show PreExpr where
    show (Var x) = unpack $ tName x
    show (Con k) = unpack $ tName k
    show (Fun f) = unpack $ tName f
    show (PrExHole h) = "[ ]"
    show (UnOp op preExp) = unpack (tName op) ++ "(" ++ show preExp ++ ")"
    show (BinOp op preExp0 preExp1) = "(" ++ show preExp0 ++ ")" ++ unpack (tName op)
                ++ "(" ++ show preExp1 ++ ")"
    show (App preExp0 preExp1) = "(" ++ show preExp0 ++ ")" ++
                                 "(" ++ show preExp1 ++ ")"
    show (Quant qua var preExp0 preExp1) = "(" ++ unpack (tName qua) ++ ")" ++ 
                                           "(" ++ unpack (tName var) ++ ") in " ++ 
                                           "(" ++ show preExp0 ++ ") | " ++ 
                                           "(" ++ show preExp1 ++ ")"
    show (Paren preExp) = "[" ++ show preExp ++ "]"

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
toExpr (preExp, Top) = preExp
toExpr (preExp, UnOpD op path) = toExpr (UnOp op preExp, path)
toExpr (preExp, BinOpL op path preExp0) = toExpr (BinOp op preExp preExp0, path)
toExpr (preExp, BinOpR op preExp0 path) = toExpr (BinOp op preExp0 preExp, path)
toExpr (preExp, AppL path preExp0) = toExpr (App preExp preExp0, path)
toExpr (preExp, AppR preExp0 path) = toExpr (App preExp0 preExp, path)
toExpr (preExp, QuantL qua var path preExp0) = 
    toExpr (Quant qua var preExp preExp0, path)
toExpr (preExp, QuantR qua var preExp0 path) = 
    toExpr (Quant qua var preExp0 preExp, path)
toExpr (preExp, ParenD path) = toExpr (Paren preExp, path)

toFocus :: PreExpr -> Focus
toFocus e = (e,Top)

-- Funcion auxiliar para calcular la lista de todos los focus de una expresion
-- dado un focus inicial. En nuestro caso particular la llamamos con (preExp, Top)
-- donde preExp es la expresion de la que queremos la lista de focus posibles.
focusToFocuses :: Maybe Focus -> [Focus]
focusToFocuses Nothing = []
focusToFocuses (Just (Var (Variable varName varTy), path)) = 
    [(Var (Variable varName varTy), path)]
focusToFocuses (Just (Con (Constant conName conTy), path)) = 
    [(Con (Constant conName conTy), path)]
focusToFocuses (Just (Fun (Func funcName funcTy), path)) = 
    [(Fun (Func funcName funcTy), path)]
focusToFocuses (Just (PrExHole (Hole holeTy), path)) = 
    [(PrExHole (Hole holeTy), path)]
focusToFocuses (Just focus) = 
    case focus of
        (UnOp op preExp, path) -> 
            ((preExp, UnOpD op path) : focusToFocuses (goDown focus))
        (BinOp op preExp0 preExp1, path) -> 
            ((preExp0, BinOpL op path preExp1) : focusToFocuses (goDownL focus)) ++
            ((preExp1, BinOpR op preExp0 path) : focusToFocuses (goDownR focus))
        (App preExp0 preExp1, path) ->
            ((preExp0, AppL path preExp1) : focusToFocuses (goDownL focus)) ++
            ((preExp1, AppR preExp0 path) : focusToFocuses (goDownR focus))
        (Quant qua var preExp0 preExp1, path) ->
            ((preExp0, QuantL qua var path preExp1) : focusToFocuses (goDownL focus)) ++
            ((preExp1, QuantR qua var preExp0 path) : focusToFocuses (goDownR focus))
        (Paren preExp, path) ->
            (preExp, ParenD path) : focusToFocuses (goDown focus)

-- Propiedades (forall e):
--   forall t \in toFocuses e, toExpr t = e
toFocuses :: PreExpr -> [Focus]
toFocuses preExp = (preExp, Top) : focusToFocuses (Just (preExp, Top))

-- Reemplaza la expresión enfocada por una nueva expresión.
replace :: Focus -> PreExpr -> Focus
replace (_,p) e' = (e',p)

-- Bajar un nivel en el focus, yendo por izquierda.
goDownL :: Focus -> Maybe Focus
goDownL = goDown

-- Bajar un nivel en el focus, yendo por derecha.
goDownR :: Focus -> Maybe Focus
goDownR f = goDown f >>= goRight

-- Navegación dentro de un Zipper: TODO (ver el artículo).
goDown :: Focus -> Maybe Focus
goDown (Var (Variable _ _), _) = Nothing
goDown (Con (Constant _ _), _) = Nothing
goDown (Fun (Func _ _), _) = Nothing
goDown (PrExHole (Hole _), _) = Nothing
goDown (UnOp op preExp, path) = Just (preExp, UnOpD op path)
goDown (BinOp op preExp0 preExp1, path) = Just (preExp0, BinOpL op path preExp1)
goDown (App preExp0 preExp1, path) = Just (preExp0, AppL path preExp1)
goDown (Quant qua var preExp0 preExp1, path) = Just (preExp0, QuantL qua var path preExp1)
goDown (Paren preExp, path) = Just (preExp, ParenD path)

goUp :: Focus -> Maybe Focus
goUp (_, Top) = Nothing
goUp (preExp, UnOpD op path) = Just (UnOp op preExp, path)
goUp (preExp, BinOpL op path preExp0) = Just (BinOp op preExp preExp0, path)
goUp (preExp, BinOpR op preExp0 path) = Just (BinOp op preExp0 preExp, path)
goUp (preExp, AppL path preExp0) = Just (App preExp preExp0, path)
goUp (preExp, AppR preExp0 path) = Just (App preExp0 preExp, path)
goUp (preExp, QuantL qua var path preExp0) = Just (Quant qua var preExp preExp0, path)
goUp (preExp, QuantR qua var preExp0 path) = Just (Quant qua var preExp0 preExp, path)
goUp (preExp, ParenD path) = Just (Paren preExp, path)

goLeft :: Focus -> Maybe Focus
goLeft (_, Top) = Nothing
goLeft (_, UnOpD _ _) = Nothing
goLeft (_, BinOpL _ _ _) = Nothing
goLeft (preExp, BinOpR op preExp0 path) = Just (preExp0, BinOpL op path preExp)
goLeft (_, AppL _ _) = Nothing
goLeft (preExp, AppR preExp0 path) = Just (preExp0, AppL path preExp)
goLeft (_, QuantL _ _ _ _) = Nothing
goLeft (preExp, QuantR qua var preExp0 path) = Just (preExp0, QuantL qua var path preExp)
goLeft (_, ParenD _) = Nothing

goRight :: Focus -> Maybe Focus
goRight (_, Top) = Nothing
goRight (_, UnOpD _ _) = Nothing
goRight (preExp, BinOpL op path preExp0) = Just (preExp0, BinOpR op preExp path)
goRight (_, BinOpR _ _ _) = Nothing
goRight (preExp, AppL path preExp0) = Just (preExp0, AppR preExp path)
goRight (_, AppR _ _) = Nothing
goRight (preExp, QuantL qua var path preExp0) = Just (preExp0, QuantR qua var preExp path)
goRight (_, QuantR _ _ _ _) = Nothing
goRight (_, ParenD _) = Nothing
