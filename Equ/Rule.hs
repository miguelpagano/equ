-- | Este módulo define el tipo de las reglas de re-escritura.

module Equ.Rule where
    
import Equ.Expr
import Equ.Types

import Data.Text    

-- | Nombres de las relaciones entre pasos de una demostracion
data RelName = Eq       -- ^ Igualdad polimorfica excepto para formulas
               | Equiv  -- ^ FOL: equivalencia
               | Impl   -- ^ FOL: implicacion
               | Cons   -- ^ FOL: consecuencia
    deriving (Eq, Show)

-- | Relaciones entre pasos de una demostracion
data Relation = Relation {
      relRepr :: Text
    , relName :: RelName
    , relTy   :: Type -- ^ Este es el tipo de las cosas relacionadas.  
    }
    deriving (Eq, Show)

-- | Constructores de las diferentes relaciones
relEq :: Relation
relEq = Relation { relRepr = pack "="
                 , relName = Eq
                 , relTy = tyVar "A"
                 }

relEquiv :: Relation
relEquiv = Relation { relRepr = pack "≡"
                    , relName = Equiv
                    , relTy = tyBool
                    }

relImpl :: Relation
relImpl = Relation { relRepr = pack "⇒"
                   , relName = Impl
                   , relTy = tyBool
                   }

relCons :: Relation
relCons = Relation { relRepr = pack "⇐"
                   , relName = Cons
                   , relTy = tyBool
                   }
    
-- | Regla de reescritura
data Rule = Rule {
      lhs :: Expr
    , rhs :: Expr
    , rel :: Relation  
    , name :: Text
    , desc :: Text
    }
    deriving (Eq,Show)
