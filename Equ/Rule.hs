-- | Este módulo define el tipo de las reglas de re-escritura.

module Equ.Rule where
    
import Equ.Expr
import Equ.Type

import Data.Text    

data Relation = Relation {
      relName :: Text
    , relTy   :: Type -- ^ Este es el tipo de las cosas relacionadas.  
    }

data Rule = Rule {
      rhs :: Expr
    , lhs :: Expr
    , rel :: Relation  
    }