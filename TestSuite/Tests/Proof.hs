module TestSuite.Tests.Proof (
            prop_serialization
            )
    where

import Equ.Proof

-- ///// ESTA SOLAMENTE PARA CORRER LOS EJEMPLOS DEL FINAL.
import Equ.PreExpr
import Equ.Rule
import Data.Text
import Equ.Parser
import Equ.Types
-- /////

prop_serialization :: Proof -> Bool
prop_serialization p = p == (decode . encode) p

-- /////////////////////////// EJEMPLOS ///////////////////////////

eq = Relation {relRepr = pack "t9", relName = Eq, relTy = TyList (TyAtom ATyNum)}
impl = Relation {relRepr = pack "t49", relName = Impl, relTy = TyAtom ATyInt}

{- Tenemos dos pruebas;

p_FxEqY:
    (F (x),Top)
Eq  {?}
    (y, Top)

p_FxEqZ:
    (F (x),Top)
Eq  {...}
    (z, Top)

y añadimos un paso, luego;

p_FxEqYEqZ:
    (F (x),Top)
Eq {...}
    (z,Top)
Eq {?}
    (y,Top)
-}

f_Fx = toFocus $ parser "F@x"
f_Fy = toFocus $ parser "F@y"
f_y = toFocus $ parser "y"
f_z = toFocus $ parser "z"

p_FxEqY = newProof eq f_Fx f_y
p_FxEqZ = newProof eq f_Fx f_z

p_FxEqZEqY = addStep (toProofFocus p_FxEqY) p_FxEqZ

{- Tenemos dos pruebas;

p_FxEqY:
    (F (x),Top)
Eq  {?}
    (y, Top)

p_YEqZ:
    (y,Top)
Eq  {...}
    (z, Top)

y añadimos un paso, luego;

p_FxEqYEqZ:
    (F (x),Top)
Eq {...}
    (y,Top)
Eq {?}
    (z,Top)
-}

p_YEqZ = newProof eq f_y f_z

p_FxEqYEqZ = addStep (toProofFocus p_FxEqY) p_YEqZ

{- Intento de añadir un paso con relaciones distintas;

p_FxEqY:
    (F (x),Top)
Eq  {?}
    (y, Top)

p_FxImplZ:
    (F (x),Top)
Impl  {...}
    (z, Top)

luego si añadimos un paso;
ClashRelation eq impl
-}

p_FxImplZ = newProof impl f_Fx f_z

p_ClashRel = addStep (toProofFocus p_FxEqY) p_FxImplZ

{- Intento de añadir un paso en donde ninguna de las expresiones de los focus
    coincide;

p_FxEqY:
    (F (x),Top)
Eq  {?}
    (y, Top)

p_FyEqZ:
    (F (y),Top)
Impl  {...}
    (z, Top)

luego si añadimos un paso;
ClashAddStep p_FxEqY p_FyEqZ
-}

p_FyEqZ = newProof eq f_Fy f_z

p_ClashAddStep = addStep (toProofFocus p_FxEqY) p_FyEqZ
