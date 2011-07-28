-- | El modulo de constructores de listas y sus símbolos de
-- función.

module Equ.Theories.List where
    
import Prelude hiding (concat,take,drop,length,sum)
import Equ.Syntax
import Equ.Types
import Equ.Expr
import Equ.PreExpr
import Equ.Rule
import Equ.Theories.AbsName

import Data.Text (pack)

import Equ.Theories.Arith (zero,successor,sum)

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
                      
listLength :: Operator
listLength = Operator { opRepr = pack "#"
                    , opName = Length
                    , opTy = tyListVar "A" :-> TyAtom ATyNat
                    }

listTake :: Operator
listTake = Operator { opRepr = pack "↑"
                    , opName = Take
                    , opTy = tyListVar "A" :-> TyAtom ATyNat :-> tyListVar "A"
                    }

listDrop :: Operator
listDrop = Operator { opRepr = pack "↓"
                    , opName = Drop
                    , opTy = tyListVar "A" :-> TyAtom ATyNat :-> tyListVar "A"
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

-- | Constructor de length
length :: Expr -> Expr
length (Expr xs) = Expr $ UnOp listLength xs

-- | Constructor de take
take :: Expr -> Expr -> Expr
take (Expr xs) (Expr n) = Expr $ BinOp listTake xs n

-- | Constructor de drop
drop :: Expr -> Expr -> Expr
drop (Expr xs) (Expr n) = Expr $ BinOp listDrop xs n

-- | Constructor de index
index :: Expr -> Expr -> Expr
index (Expr xs) (Expr n) = Expr $ BinOp listIndex xs n

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


-- Reglas para la definicion de length (#)
emptyLength :: Rule
emptyLength = Rule { lhs = length emptyList
                   , rhs = zero
                   , rel = relEq
                   , desc = pack ""
                   }

consLength :: Rule
consLength = Rule { lhs = length (append varX varXS)
                  , rhs = successor (length varXS)
                  , rel = relEq
                  , desc = pack ""
                  }
    where varX = Expr $ Var $ var "x" $ tyVar "A"
          varXS = varList "xs" "A"

-- Reglas para la definicion de take
zeroTake :: Rule
zeroTake = Rule { lhs = take varXS zero
                , rhs = emptyList
                , rel = relEq
                , desc = pack ""
                }
    where varXS = varList "xs" "A"
                      
                
emptyTake :: Rule
emptyTake = Rule { lhs = take emptyList varN
                 , rhs = emptyList
                 , rel = relEq
                 , desc = pack ""
                 }
    where varN = Expr $ Var $ var "x" $ TyAtom ATyNat

consTake :: Rule
consTake = Rule { lhs = take (append varX varXS) (successor varN)
                , rhs = append varX $ take varXS varN
                , rel = relEq
                , desc = pack ""
                }
    where varXS = varList "xs" "A"
          varX = Expr $ Var $ var "x" $ tyVar "A"
          varN = Expr $ Var $ var "x" $ TyAtom ATyNat
          

-- Reglas para la definicion de drop
zeroDrop :: Rule
zeroDrop = Rule { lhs = drop varXS zero
                , rhs = varXS
                , rel = relEq
                , desc = pack ""
                }
    where varXS = varList "xs" "A"
                
emptyDrop :: Rule
emptyDrop = Rule { lhs = drop emptyList varN
                 , rhs = emptyList
                 , rel = relEq
                 , desc = pack ""
                 }
    where varN = Expr $ Var $ var "x" $ TyAtom ATyNat

consDrop :: Rule
consDrop = Rule { lhs = drop (append varX varXS) (successor varN)
                , rhs = drop varXS varN
                , rel = relEq
                , desc = pack ""
                }
    where varXS = varList "xs" "A"
          varX = Expr $ Var $ var "x" $ tyVar "A"
          varN = Expr $ Var $ var "x" $ TyAtom ATyNat
          
-- Reglas para la definicion de Index
zeroIndex :: Rule
zeroIndex = Rule { lhs = index (append varX varXS) zero
                 , rhs = varX
                 , rel = relEq
                 , desc = pack ""
                 }
    where varXS = varList "xs" "A"
          varX = Expr $ Var $ var "x" $ tyVar "A"
