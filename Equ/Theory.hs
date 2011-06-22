-- | A Theory is a set of valid expressions together with
-- a set of axioms. 
module Equ.Theory where
    
import Data.Text
import Equ.Expr
import Equ.Rule
-- import Equ.Proof
    
-- Un axioma
data Axiom = Axiom {
      axName  :: Text
    , axExpr  :: Expr
    , axRules :: [Rule]
    }
    
-- Un teorema
data Theorem = Theorem {
      thName  :: Text
    , thExpr  :: Expr
--    , thProof :: Proof
    , thRules :: [Rule]
    }


