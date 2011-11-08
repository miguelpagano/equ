-- Los zippers pueden ser convenientes; la referencia es: ``The
-- Zipper'' de G&#233;rard Huet en JFP. 

module Equ.PreExpr.Zipper 
    ( Focus
    , Path
    , toExpr, toFocus, toFocuses
    , replace
    , goDown, goUp, goLeft, goRight, goDownR, goDownL
    ) where

import Equ.PreExpr.Internal
import Equ.Syntax

import Data.Serialize(Serialize, get, getWord8, put, putWord8)

import Control.Applicative ((<$>), (<*>),Applicative(..))
import Test.QuickCheck(Arbitrary, arbitrary, oneof)

-- | Definici&#243;n de los posibles lugares en los que podemos estar
-- enfoc&#225;ndonos.
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

instance Serialize Path where
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
        1 -> UnOpD <$> get <*> get
        2 -> BinOpL <$> get <*> get <*> get 
        3 -> BinOpR <$> get <*> get <*> get
        4 -> AppL <$> get <*> get
        5 -> AppR <$> get <*> get
        6 -> QuantL <$> get <*> get <*> get <*> get
        7 -> QuantR <$> get <*> get <*> get <*> get
        8 -> ParenD <$> get
        _ -> fail $ "SerializeErr Path " ++ show tag_

-- | Un Focus representa la expresi&#243;n que consiste de completar el
-- hueco denotado por Path con la expresi&#243;n PreExpr (eso es lo que
-- hace toExpr).
type Focus = (PreExpr,Path)

toExpr :: Focus -> PreExpr
toExpr (pe, Top) = pe
toExpr (pe, UnOpD op path) = toExpr (UnOp op pe, path)
toExpr (pe, BinOpL op path pe0) = toExpr (BinOp op pe pe0, path)
toExpr (pe, BinOpR op pe0 path) = toExpr (BinOp op pe0 pe, path)
toExpr (pe, AppL path pe0) = toExpr (App pe pe0, path)
toExpr (pe, AppR pe0 path) = toExpr (App pe0 pe, path)
toExpr (pe, QuantL qua v path pe0) = 
    toExpr (Quant qua v pe pe0, path)
toExpr (pe, QuantR qua v pe0 path) = 
    toExpr (Quant qua v pe0 pe, path)
toExpr (pe, ParenD path) = toExpr (Paren pe, path)

-- | Dado una expresi&#243;n la enfocamos. Es decir luego de llamar a toFocus con 
-- preExp queda el focus que tiene a la expresi&#243;n y estamos en el Top.
toFocus :: PreExpr -> Focus
toFocus e = (e,Top)

-- Funcion auxiliar para calcular la lista de todos los focus de una expresion
-- dado un focus inicial. En nuestro caso particular la llamamos con (preExp, Top)
-- donde preExp es la expresion de la que queremos la lista de focus posibles.
-- Nota: En cada llamada recursiva, el elemento que agregamos en a la lista
-- es el respectivo elemento que devuelve (go* focus), * in {Down, DownR, DownL}.
focusToFocuses :: Maybe Focus -> [Focus]
focusToFocuses Nothing = []
focusToFocuses (Just f) = 
            case (goDownL f, goDownR f) of
                (glf@(Just lf), grf@(Just rf)) -> (lf : focusToFocuses glf) ++
                                                    (rf : focusToFocuses grf)
                (glf@(Just lf), Nothing) -> lf : focusToFocuses glf
                (Nothing, _) -> []

-- | Dado una preExpresion obtenemos todas las subexpresiones navegando con el
-- zipper.
-- Propiedades (forall e):
--   forall t \in toFocuses e, toExpr t = e
toFocuses :: PreExpr -> [Focus]
toFocuses pe = (pe, Top) : focusToFocuses (Just (pe, Top))

-- | Reemplaza la expresi&#243;n enfocada por una nueva expresi&#243;n.
replace :: Focus -> PreExpr -> Focus
replace (_,p) e' = (e',p)

-- Bajar un nivel en el focus, yendo por izquierda.
goDownL :: Focus -> Maybe Focus
goDownL = goDown

-- Bajar un nivel en el focus, yendo por derecha.
goDownR :: Focus -> Maybe Focus
goDownR f = goDown f >>= goRight

-- Navegaci&#243;n dentro de un Zipper.
-- | Bajar un nivel en el focus.
goDown :: Focus -> Maybe Focus
goDown (Var _, _) = Nothing
goDown (Con _, _) = Nothing
goDown (Fun _, _) = Nothing
goDown (PrExHole _, _) = Nothing
goDown (UnOp op pe, path) = Just (pe, UnOpD op path)
goDown (BinOp op pe0 pe1, path) = Just (pe0, BinOpL op path pe1)
goDown (App pe0 pe1, path) = Just (pe0, AppL path pe1)
goDown (Quant qua v pe0 pe1, path) = Just (pe0, QuantL qua v path pe1)
goDown (Paren pe, path) = Just (pe, ParenD path)

-- | Subir un nivel en el focus.
goUp :: Focus -> Maybe Focus
goUp (_, Top) = Nothing
goUp (pe, UnOpD op path) = Just (UnOp op pe, path)
goUp (pe, BinOpL op path pe0) = Just (BinOp op pe pe0, path)
goUp (pe, BinOpR op pe0 path) = Just (BinOp op pe0 pe, path)
goUp (pe, AppL path pe0) = Just (App pe pe0, path)
goUp (pe, AppR pe0 path) = Just (App pe0 pe, path)
goUp (pe, QuantL qua v path pe0) = Just (Quant qua v pe pe0, path)
goUp (pe, QuantR qua v pe0 path) = Just (Quant qua v pe0 pe, path)
goUp (pe, ParenD path) = Just (Paren pe, path)

-- | Ir a la izquierda en un focus, sin cambiar de nivel.
goLeft :: Focus -> Maybe Focus
goLeft (_, Top) = Nothing
goLeft (_, UnOpD _ _) = Nothing
goLeft (_, BinOpL _ _ _) = Nothing
goLeft (pe, BinOpR op pe0 path) = Just (pe0, BinOpL op path pe)
goLeft (_, AppL _ _) = Nothing
goLeft (pe, AppR pe0 path) = Just (pe0, AppL path pe)
goLeft (_, QuantL _ _ _ _) = Nothing
goLeft (pe, QuantR qua v pe0 path) = Just (pe0, QuantL qua v path pe)
goLeft (_, ParenD _) = Nothing

-- | Ir a la derecha en un focus, sin cambiar de nivel.
goRight :: Focus -> Maybe Focus
goRight (_, Top) = Nothing
goRight (_, UnOpD _ _) = Nothing
goRight (pe, BinOpL op path pe0) = Just (pe0, BinOpR op pe path)
goRight (_, BinOpR _ _ _) = Nothing
goRight (pe, AppL path pe0) = Just (pe0, AppR pe path)
goRight (_, AppR _ _) = Nothing
goRight (pe, QuantL qua v path pe0) = Just (pe0, QuantR qua v pe path)
goRight (_, QuantR _ _ _ _) = Nothing
goRight (_, ParenD _) = Nothing
