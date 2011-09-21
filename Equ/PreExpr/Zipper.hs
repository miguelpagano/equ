-- Los zippers pueden ser convenientes; la referencia es: ``The
-- Zipper'' de Gérard Huet en JFP. 

module Equ.PreExpr.Zipper 
    ( Focus
    , Path
    , toExpr, toFocus, toFocuses
    , replace
    , goDown, goUp, goLeft, goRight, goDownR, goDownL
    ) where

import Equ.PreExpr.Internal
import Equ.Syntax

import Data.Binary

import Control.Applicative ((<$>), (<*>),Applicative(..))
import Test.QuickCheck(Arbitrary, arbitrary, oneof)

-- | Definición de los posibles lugares en los que podemos estar
-- enfocándonos.
data Path = Top
          | UnOpD Operator Path
          | BinOpL Operator Path PreExpr
          | BinOpR Operator PreExpr Path
          | AppL Path PreExpr
          | AppR PreExpr Path
          | QuantL Quantifier Variable Path PreExpr
          | QuantR Quantifier Variable PreExpr Path 
          | ParenD Path
            deriving (Eq,Show)

instance Arbitrary Path where
    arbitrary =
        oneof [ return Top
              , UnOpD <$> arbitrary <*> arbitrary
              , BinOpL <$> arbitrary <*> arbitrary <*> arbitrary
              , BinOpR <$> arbitrary <*> arbitrary <*> arbitrary
              , AppL <$> arbitrary <*> arbitrary
              , AppR <$> arbitrary <*> arbitrary
              , QuantL <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
              , QuantR <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
              , ParenD <$> arbitrary
              ]

instance Binary Path where
    put Top = putWord8 0
    put (UnOpD op p) = putWord8 1 >> put op >> put p
    put (BinOpL op p pe) = putWord8 2 >> put op >> put p >> put pe
    put (BinOpR op pe p) = putWord8 3 >> put op >> put pe >> put p
    put (AppL p pe) = putWord8 4 >> put p >> put pe
    put (AppR pe p) = putWord8 5 >> put pe >> put p
    put (QuantL q v p pe) = putWord8 6 >> put q >> put v >> put p >> put pe
    put (QuantR q v pe p) = putWord8 7 >> put q >> put v >> put pe >> put p
    put (ParenD p) = putWord8 8 >> put p

    get = do
    tag_ <- getWord8
    case tag_ of
        0 -> return Top
        1 -> get >>= \op -> get >>= \p -> return (UnOpD op p)
        2 -> get >>= \op -> get >>= \p -> get >>= \pe -> return (BinOpL op p pe) 
        3 -> get >>= \op -> get >>= \pe -> get >>= \p -> return (BinOpR op pe p)
        4 -> get >>= \p -> get >>= \pe -> return (AppL p pe)
        5 -> get >>= \pe -> get >>= \p -> return (AppR pe p)
        6 -> get >>= \q -> get >>= \v -> get >>= 
                     \p -> get >>= \pe -> return (QuantL q v p pe)
        7 -> get >>= \q -> get >>= \v -> get >>= 
                     \pe -> get >>= \p -> return (QuantR q v pe p)
        8 -> get >>= return . ParenD
        _ -> fail "Problem: Instance Binary Path."

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
toExpr (preExp, QuantL qua v path preExp0) = 
    toExpr (Quant qua v preExp preExp0, path)
toExpr (preExp, QuantR qua v preExp0 path) = 
    toExpr (Quant qua v preExp0 preExp, path)
toExpr (preExp, ParenD path) = toExpr (Paren preExp, path)

-- | Dado una expresión la enfocamos. Es decir luego de llamar a toFocus con 
-- preExp queda el focus que tiene a la expresión y estamos en el Top.
toFocus :: PreExpr -> Focus
toFocus e = (e,Top)

-- Funcion auxiliar para calcular la lista de todos los focus de una expresion
-- dado un focus inicial. En nuestro caso particular la llamamos con (preExp, Top)
-- donde preExp es la expresion de la que queremos la lista de focus posibles.
-- Nota: En cada llamada recursiva, el elemento que agregamos en a la lista
-- es el respectivo elemento que devuelve (go* focus), * in {Down, DownR, DownL}.
focusToFocuses :: Maybe Focus -> [Focus]
focusToFocuses Nothing = []
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
        (Quant qua v preExp0 preExp1, path) ->
            ((preExp0, QuantL qua v path preExp1) : focusToFocuses (goDownL focus)) ++
            ((preExp1, QuantR qua v preExp0 path) : focusToFocuses (goDownR focus))
        (Paren preExp, path) ->
            (preExp, ParenD path) : focusToFocuses (goDown focus)
        _ -> [] -- El wildcard simboliza los casos de var, const, fun y hole.
                -- El detalle a comentar es que si llegamos a uno de esos casos
                -- no lo agregamos en la lista porque en la llamada anterior
                -- de la funcion focusToFocuses es donde agregamos.

-- | Dado una preExpresion obtenemos todas las subexpresiones navegando con el
-- zipper.
-- Propiedades (forall e):
--   forall t \in toFocuses e, toExpr t = e
toFocuses :: PreExpr -> [Focus]
toFocuses preExp = (preExp, Top) : focusToFocuses (Just (preExp, Top))

-- | Reemplaza la expresión enfocada por una nueva expresión.
replace :: Focus -> PreExpr -> Focus
replace (_,p) e' = (e',p)

-- Bajar un nivel en el focus, yendo por izquierda.
goDownL :: Focus -> Maybe Focus
goDownL = goDown

-- Bajar un nivel en el focus, yendo por derecha.
goDownR :: Focus -> Maybe Focus
goDownR f = goDown f >>= goRight

-- Navegación dentro de un Zipper.
-- | Bajar un nivel en el focus.
goDown :: Focus -> Maybe Focus
goDown (Var _, _) = Nothing
goDown (Con _, _) = Nothing
goDown (Fun _, _) = Nothing
goDown (PrExHole _, _) = Nothing
goDown (UnOp op preExp, path) = Just (preExp, UnOpD op path)
goDown (BinOp op preExp0 preExp1, path) = Just (preExp0, BinOpL op path preExp1)
goDown (App preExp0 preExp1, path) = Just (preExp0, AppL path preExp1)
goDown (Quant qua v preExp0 preExp1, path) = Just (preExp0, QuantL qua v path preExp1)
goDown (Paren preExp, path) = Just (preExp, ParenD path)

-- | Subir un nivel en el focus.
goUp :: Focus -> Maybe Focus
goUp (_, Top) = Nothing
goUp (preExp, UnOpD op path) = Just (UnOp op preExp, path)
goUp (preExp, BinOpL op path preExp0) = Just (BinOp op preExp preExp0, path)
goUp (preExp, BinOpR op preExp0 path) = Just (BinOp op preExp0 preExp, path)
goUp (preExp, AppL path preExp0) = Just (App preExp preExp0, path)
goUp (preExp, AppR preExp0 path) = Just (App preExp0 preExp, path)
goUp (preExp, QuantL qua v path preExp0) = Just (Quant qua v preExp preExp0, path)
goUp (preExp, QuantR qua v preExp0 path) = Just (Quant qua v preExp0 preExp, path)
goUp (preExp, ParenD path) = Just (Paren preExp, path)

-- | Ir a la izquierda en un focus, sin cambiar de nivel.
goLeft :: Focus -> Maybe Focus
goLeft (_, Top) = Nothing
goLeft (_, UnOpD _ _) = Nothing
goLeft (_, BinOpL _ _ _) = Nothing
goLeft (preExp, BinOpR op preExp0 path) = Just (preExp0, BinOpL op path preExp)
goLeft (_, AppL _ _) = Nothing
goLeft (preExp, AppR preExp0 path) = Just (preExp0, AppL path preExp)
goLeft (_, QuantL _ _ _ _) = Nothing
goLeft (preExp, QuantR qua v preExp0 path) = Just (preExp0, QuantL qua v path preExp)
goLeft (_, ParenD _) = Nothing

-- | Ir a la derecha en un focus, sin cambiar de nivel.
goRight :: Focus -> Maybe Focus
goRight (_, Top) = Nothing
goRight (_, UnOpD _ _) = Nothing
goRight (preExp, BinOpL op path preExp0) = Just (preExp0, BinOpR op preExp path)
goRight (_, BinOpR _ _ _) = Nothing
goRight (preExp, AppL path preExp0) = Just (preExp0, AppR preExp path)
goRight (_, AppR _ _) = Nothing
goRight (preExp, QuantL qua v path preExp0) = Just (preExp0, QuantR qua v preExp path)
goRight (_, QuantR _ _ _ _) = Nothing
goRight (_, ParenD _) = Nothing
