module Equ.Proof.Condition where

import Data.Serialize(Serialize, get, getWord8, put, putWord8, encode, decode)
import Control.Applicative ((<$>), (<*>))
import Test.QuickCheck
import Equ.PreExpr
import Equ.Syntax

-- | Para aplicar un paso de prueba, puede ser necesario validar algunas condiciones.
--   GenConditions son condiciones sobre la aplicación de una regla, en la cual se realiza
--   la reescritura normalmente, y luego se chequea alguna condición extra. Pueden ser varias.
--   SpecialCondition es una condición especial para algún axioma, en el cual el proceso de 
--   aplicación de la regla es diferente al general.
data Condition = GenConditions [GCondition]
               | SpecialCondition SCondition
    deriving (Eq,Show)    
 
 -- | GCondition son condiciones que se chequean al aplicar un axioma luego de 
 --   realizar la reescritura.
data GCondition = VarNotInExpr Variable PreExpr -- La variable no ocurre en la expresion
                 | NotEmptyRange PreExpr -- El Rango de cuantificación es no vacío (distinto de False).
                 | InductiveHypothesis PreExpr -- En la hipótesis inductiva, la reescritura no se hace con cualquier variable
                                              -- sino que tiene que ser exactamente con la misma variable del pattern.
    deriving (Eq,Show)
 
data SCondition = -- Condición para el rango unitario. La variable es la cuantificada, las expresiones siguientes
                  -- corresponden a la expresion a la q se iguala la variable en el rango, al termino
                  -- y a la expresion derecha.
                   UnitRangeC Variable PreExpr PreExpr PreExpr
                 | ChangeVarC Variable PreExpr PreExpr --Condición para el cambio de variable. La variable es la nueva cuantificada
                                                       -- las dos expresiones son el rango y el término.
    deriving (Eq,Show)
 
instance Arbitrary Condition where
    arbitrary = oneof [ GenConditions <$> arbitrary
                      , SpecialCondition <$> arbitrary
                       ]
                   
instance Serialize Condition where
    put (GenConditions lc) = putWord8 0 >> put lc
    put (SpecialCondition sc) = putWord8 1 >> put sc
    
    get = getWord8 >>= \tag ->
        case tag of
             0 -> GenConditions <$> get
             1 -> SpecialCondition <$> get
                   
                   
instance Arbitrary GCondition where
    arbitrary = oneof [ VarNotInExpr <$> arbitrary <*> arbitrary
                      , NotEmptyRange <$> arbitrary
                      , InductiveHypothesis <$> arbitrary
                      ]
                   
instance Serialize GCondition where
    put (VarNotInExpr v p) = putWord8 0 >> put v >> put p
    put (NotEmptyRange p) = putWord8 1 >> put p
    put (InductiveHypothesis v)= putWord8 2 >> put v
    
    get = getWord8 >>= \tag_ ->
        case tag_ of
             0 -> VarNotInExpr <$> get <*> get
             1 -> NotEmptyRange <$> get
             2 -> InductiveHypothesis <$> get
        
instance Arbitrary SCondition where
    arbitrary = oneof [ UnitRangeC <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
                      , ChangeVarC <$> arbitrary <*> arbitrary <*> arbitrary
                      ]
                      
instance Serialize SCondition where
    put (UnitRangeC v p p' p'') = putWord8 0 >> put v >> put p >> put p' >> put p''
    put (ChangeVarC v p p') = putWord8 1 >> put v >> put p >> put p'
    
    get = getWord8 >>= \tag ->
        case tag of
             0 -> UnitRangeC <$> get <*> get <*> get <*> get
             1 -> ChangeVarC <$> get <*> get <*> get
                      
                      