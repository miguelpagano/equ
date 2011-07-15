-- | El modulo de constructores de listas y sus símbolos de
-- función.

module Equ.Theories.List where
    
import Prelude hiding (concat)
import Equ.Syntax
import Equ.Types
import Equ.Expr
import Equ.PreExpr
import Equ.Rule
import Equ.Theories.AbsName

import Data.Text (pack)
    
-- | Constructor del tipo de listas polimorficas; el string indica el
-- nombre de la variable de tipo
tyListVar :: String -> Type
tyListVar = TyList . tyVar

listEmpty :: Constant
listEmpty = Constant { conRepr = pack "[ ]"
                     , conName = Empty
                     , conTy = tyListVar "A"
                     }
            
listApp :: Operator
listApp = Operator { opRepr = pack "▹"
                   , opName = Append
                   , opTy = tyVar "A" :-> tyListVar "A" :-> tyListVar "A"
                   }  
                  
listIndex :: Operator
listIndex = Operator { opRepr = pack "."
                     , opName = Index
                     , opTy = tyListVar "A" :-> TyAtom ATyNat :-> tyVar "A"
                     }
                     
listConcat :: Operator
listConcat = Operator { opRepr = pack "++"
                      , opName = Concat
                      , opTy = tyListVar "A" :-> tyListVar "A" :-> tyListVar "A"
                      }

-- | Constructor de variable de tipo lista polimorfica; el primer string es
-- el nombre de la variable, el segundo el nombre de la variable de tipo
varList :: String -> String -> Expr
varList s t = Expr $ Var $ listVar s t
    where listVar s t = var s $ tyListVar t 

-- | Constructor de lista vacia
emptyList :: Expr
emptyList = Expr $ Con $ listEmpty

-- | Constructor de insercion por izquierda
-- PRE: Las expresiones son del tipo adecuado
append :: Expr -> Expr -> Expr
append (Expr x) (Expr xs) = Expr $ BinOp listApp x xs

-- | Constructor de concatenacion
concat :: Expr -> Expr -> Expr
concat (Expr xs) (Expr ys) = Expr $ BinOp listConcat xs ys

emptyConcat :: Rule
emptyConcat = Rule { lhs = concat emptyList varYS
                   , rhs = varYS
                   , rel = relEq
                   , desc = pack ""
                   }
    where varYS = varList "ys" "A"
                          
consConcat :: Rule
consConcat = Rule { lhs = concat (append varX varXS) varYS
                  , rhs = append varX (concat varXS varYS)
                  , rel = relEq
                  , desc = pack ""
                  }
    where varX = Expr $ Var $ var "x" $ tyVar "A"
          varXS = varList "xs" "A"
          varYS = varList "ys" "A"
