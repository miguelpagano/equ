-- | El módulo de expresiones de fórmulas de primer orden.

module Equ.Theories.FOL where

import Prelude hiding (and,or) 
import Equ.Syntax
import Equ.Types
import Equ.Expr
import Equ.PreExpr
import Equ.Rule
import Equ.Theories.AbsName

import Data.Text (pack)


-- CONSTANTES

folTrue :: Constant
folTrue = Constant { conRepr = pack "True"
                   , conName = CTrue
                   , conTy = tyBool
                   }
                     
folFalse :: Constant
folFalse = Constant { conRepr = pack "False"
                    , conName = CFalse
                    , conTy = tyBool
                    }
                     
-- CUANTIFICADORES

folForall :: Quantifier
folForall = Quantifier { quantRepr = pack "∀"
                       , quantName = Forall
                       , quantTy = tyVar "A" :-> tyBool
                       }
                    
folExist :: Quantifier
folExist = Quantifier { quantRepr = pack "∃"
                      , quantName = Exist
                      , quantTy = tyVar "A" :-> tyBool
                      }

-- OPERACIONES

-- Tipo de las operaciones logicas
folBinOpType = tyBool :-> tyBool :-> tyBool
folUnOpType = tyBool :-> tyBool

-- Equivalencia
folEquiv :: Operator
folEquiv = Operator { opRepr = pack "≡"
                    , opName = Equival
                    , opTy = folBinOpType
                    }
                    
-- Discrepancia
folDiscrep :: Operator
folDiscrep = Operator { opRepr = pack "≢"
                      , opName = Discrep
                      , opTy = folBinOpType
                      }

-- And
folAnd :: Operator
folAnd = Operator { opRepr = pack "∧"
                  , opName = And
                  , opTy = folBinOpType
                  }

-- Or
folOr :: Operator
folOr = Operator { opRepr = pack "∨"
                 , opName = Or
                 , opTy = folBinOpType
                 }
     
-- Negacion     
folNeg :: Operator
folNeg = Operator { opRepr = pack "¬"
                  , opName = Neg
                  , opTy = folUnOpType
                  }

-- Implicación
folImpl :: Operator
folImpl = Operator { opRepr = pack "⇒"
                   , opName = Implic
                   , opTy = folBinOpType
                   }

-- Consecuencia
folConseq :: Operator
folConseq = Operator { opRepr = pack "⇐"
                    , opName = Conseq
                    , opTy = folBinOpType
                    }
                    
-- A continuacion definimos constructores de expresiones, para su facil manejo

-- | Constructor de Constantes logicas
true :: Expr
true = Expr $ Con $ folTrue

false :: Expr
false = Expr $ Con $ folFalse

-- | Constructores de Operaciones lógicas

-- Equivalencia
equiv :: Expr -> Expr -> Expr
equiv (Expr p) (Expr q) = Expr $ BinOp folEquiv p q

-- Discrepancia
discrep :: Expr -> Expr -> Expr
discrep (Expr p) (Expr q) = Expr $ BinOp folDiscrep p q

-- Negacion
neg :: Expr -> Expr
neg (Expr p) = Expr $ UnOp folNeg p

-- And
and :: Expr -> Expr -> Expr
and (Expr p) (Expr q) = Expr $ BinOp folAnd p q

-- Or
or :: Expr -> Expr -> Expr
or (Expr p) (Expr q) = Expr $ BinOp folOr p q

-- Implicacion
impl :: Expr -> Expr -> Expr
impl (Expr p) (Expr q) = Expr $ BinOp folImpl p q

-- Consecuencia
conseq :: Expr -> Expr -> Expr
conseq (Expr p) (Expr q) = Expr $ BinOp folConseq p q

-- Constructor de para todo:

-- DUDA: En el cuantificador paraTodo, y creo que en todos los cuantificadores
--       tenemos una variable y luego el rango es la aplicacion de un predicado a esa variable
--       termino es tambien la aplicacion de un predicado a esa variable. Lo cual me sugiere
--       que el constructor de forAll y exist tome una variable y dos funciones (predicados).

forAll :: Variable -> Expr -> Expr -> Expr
forAll v (Expr r) (Expr t) = Expr $ Quant folForall v r t

-- Constructor del existe:
exist :: Variable -> Expr -> Expr -> Expr
exist v (Expr r) (Expr t) = Expr $ Quant folExist v r t

-- AXIOMAS DEL CALCULO PROPOSICIONAL
-- Los axiomas del calculo proposicional son Expresiones dentro de Eq

-- Variables a usar en las reglas:
varP= Expr $ Var $ var "p" tyBool
varQ= Expr $ Var $ var "q" tyBool
varR= Expr $ Var $ var "r" tyBool

-- ============
-- EQUIVALENCIA
-- ============

-- Ascociatividad: ((p ≡ q) ≡ r) ≡ (p ≡ (q ≡ r))
-- VER CUANTAS SON LAS REGLAS QUE HAY QUE HACER PARA ESTE AXIOMA.

-- ---------------------------------
-- Conmutatividad: p ≡ q ≡ q ≡ p
-- ---------------------------------
-- Regla1: p ≡ (q ≡ (q ≡ p))
conmEquiv_Rule1 :: Rule
conmEquiv_Rule1 = Rule { lhs = varP
                  , rhs = equiv varQ (equiv varQ varP)
                  , rel = relEquiv
                  , name = pack ""
                  , desc = pack ""
                  }
 
 -- Regla2; (p ≡ q) ≡ (q ≡ p)
conmEquiv_Rule2 :: Rule
conmEquiv_Rule2 = Rule { lhs = equiv varP varQ
                       , rhs = equiv varQ varP
                       , rel = relEquiv
                       , name = pack ""
                       , desc = pack ""
                       }
                       
-- Regla3: ((p ≡ q) ≡ q) ≡ p
conmEquiv_Rule3 :: Rule
conmEquiv_Rule3 = Rule { lhs = equiv (equiv varP varQ) varQ
                       , rhs = varP
                       , rel = relEquiv
                       , name = pack ""
                       , desc = pack ""
                       }
                       
-- NOTA: No se si hace falta poner dos reglas mas, que serian:
-- (p ≡ (q ≡ q)) ≡ p
-- p ≡ ((q ≡ q) ≡ p)
-- Puesto que q ≡ q es True por Neutro de Equiv

-- ------------------------------
-- Neutro: p ≡ True ≡ p
-- ------------------------------
-- Regla1; (p ≡ True) ≡ p
neuterEquiv_Rule1 :: Rule
neuterEquiv_Rule1 = Rule { lhs = equiv varP true
                         , rhs = varP
                         , rel = relEquiv
                         , name = pack ""
                         , desc = pack ""
                         }
                         
-- Regla2: p ≡ (True ≡ p)
neuterEquiv_Rule2 :: Rule
neuterEquiv_Rule2 = Rule { lhs = varP
                         , rhs = equiv true varP
                         , rel = relEquiv
                         , name = pack ""
                         , desc = pack ""
                         }


-- =========
-- NEGACION
-- =========

-- ------------------------------
-- Negacion y Equivalencia: ¬(p ≡ q) ≡ ¬p ≡ q
-- ------------------------------
-- Regla1: ¬(p ≡ q) ≡ (¬p ≡ q)
equivNeg_Rule1 :: Rule
equivNeg_Rule1 = Rule { lhs = neg $ equiv varP varQ
                      , rhs = equiv (neg varP) varQ
                      , rel = relEquiv
                      , name = pack ""
                      , desc = pack ""
                      }
                      
-- Regla2; (¬(p ≡ q) ≡ ¬p) ≡ q
equivNeg_Rule2 :: Rule
equivNeg_Rule2 = Rule { lhs = equiv (neg $ equiv varP varQ) (neg varP)
                      , rhs = varQ
                      , rel = relEquiv
                      , name = pack ""
                      , desc = pack ""
                      }
                      
-- ------------------------------
-- Definicion de False: False ≡ ¬True
-- ------------------------------
-- Unica regla
false_Rule :: Rule
false_Rule = Rule { lhs = false
                  , rhs = neg true
                  , rel = relEquiv
                  , name = pack ""
                  , desc = pack ""
                  }

-- ============
-- DISCREPANCIA
-- ============

-- ------------------------------
-- Definicion de /≡: (p /≡ q) ≡ ¬(p ≡ q)
-- ------------------------------
-- Unica regla
discrep_Rule :: Rule
discrep_Rule = Rule { lhs = discrep varP varQ
                    , rhs = neg $ equiv varP varQ
                    , rel = relEq
                    , name = pack ""
                    , desc = pack ""
                    }
                   
-- ===========
-- DISYUNCION
-- ===========

-- ------------------------------
-- Asociatividad: (p ∨ q) ∨ r ≡ p ∨ (q ∨ r)
-- ------------------------------
asocOr_Rule :: Rule
asocOr_Rule = Rule { lhs = or (or varP varQ) varR
                  , rhs = or varP (or varQ varR)
                  , rel = relEq
                  , name = pack ""
                  , desc = pack ""
                  }
                  
-- ------------------------------
-- Conmutatividad: p ∨ q ≡ q ∨ p
-- ------------------------------
conmOr_Rule :: Rule
conmOr_Rule = Rule { lhs = or varP varQ
                  , rhs = or varQ varP
                  , rel = relEq
                  , name = pack ""
                  , desc = pack ""
                  }
                  
-- ------------------------------
-- Idempotencia: p ∨ p ≡ p
-- ------------------------------
idempotOr_Rule :: Rule
idempotOr_Rule = Rule { lhs = or varP varP
                      , rhs = varP
                      , rel = relEq
                      , name = pack ""
                      , desc = pack ""
                      }
                     
-- ------------------------------
-- Distributividad con Equivalencia: p ∨ (q ≡ r) ≡ (p ∨ q) ≡ (p ∨ r)
-- ------------------------------
-- Regla1: p ∨ (q ≡ r) ≡ ((p ∨ q) ≡ (p ∨ r))
distEqOr_Rule1 :: Rule
distEqOr_Rule1 = Rule { lhs = or varP $ equiv varQ varR
                      , rhs = equiv (or varP varQ) (or varP varR)
                      , rel = relEquiv
                      , name = pack ""
                      , desc = pack ""
                      }
                      
-- Regla2: (p ∨ (q ≡ r) ≡ (p ∨ q)) ≡ (p ∨ r)
distEqOr_Rule2 :: Rule
distEqOr_Rule2 = Rule { lhs = equiv (or varP $ equiv varQ varR) (or varP varQ)
                      , rhs = or varP varR
                      , rel = relEquiv
                      , name = pack ""
                      , desc = pack ""
                      }

-- ------------------------------
-- Tercero Excluido: p ∨ ¬p
-- ------------------------------
excludOr_Rule :: Rule
excludOr_Rule = Rule { lhs = or varP $ neg varP
                     , rhs = true
                     , rel = relEquiv
                     , name = pack ""
                     , desc = pack ""
                     }
                     

-- ===========
-- CONJUNCION
-- ===========

-- ------------------------------
-- Regla Dorada: p ∧ q ≡ p ≡ q ≡ p ∨ q
-- ------------------------------
-- Regla1: p ∧ q ≡ (p ≡ (q ≡ p ∨ q))
goldenRule1 :: Rule
goldenRule1 = Rule { lhs = and varP varQ
                   , rhs = equiv varP $ equiv varQ $ or varP varQ
                   , rel = relEquiv
                   , name = pack ""
                   , desc = pack ""
                   }
                   
-- Regla2: p ∧ q ≡ ((p ≡ q) ≡ p ∨ q)
goldenRule2 :: Rule
goldenRule2 = Rule { lhs = and varP varQ
                   , rhs = equiv (equiv varP varQ) (or varP varQ)
                   , rel = relEquiv
                   , name = pack ""
                   , desc = pack ""
                   }
                   
-- DUDA: Hace falta definir dos reglas para lo anterior? 
-- p ∧ q ≡ (p ≡ q ≡ p ∨ q)
-- Si nosotros escribimos el lado derecho de una de las dos formas posibles, luego
-- la otra forma podria ser derivada por la regla de asociatividad:
-- p ≡ (q ≡ p ∨ q) es equivalente a ((p ≡ q) ≡ p ∨ q)

-- Regla3: ((p ∧ q) ≡ p) ≡ (q ≡ p ∨ q)
goldenRule3 :: Rule
goldenRule3 = Rule { lhs = equiv (and varP varQ) varP
                   , rhs = equiv varQ $ or varP varQ
                   , rel = relEquiv
                   , name = pack ""
                   , desc = pack ""
                   }


-- Tenemos la misma cuestión sobre la asociatividad en las siguientes reglas
-- Regla4:  (p ∧ q ≡ p) ≡ q) ≡ p ∨ q
goldenRule4 :: Rule
goldenRule4 = Rule { lhs = equiv (equiv (and varP varQ) varQ) (or varP varQ)
                   , rhs = or varP varQ
                   , rel = relEquiv
                   , name = pack ""
                   , desc = pack ""
                   }
                   
-- Regla5: (p ∧ q ≡ (p ≡ q)) ≡ p ∨ q
goldenRule5 :: Rule
goldenRule5 = Rule { lhs = equiv (and varP varQ) (equiv varP varQ)
                   , rhs = or varP varQ
                   , rel = relEquiv
                   , name = pack ""
                   , desc = pack ""
                   }
                   
-- ===========
-- IMPLICACION
-- ===========

-- ------------------------------
-- Definicion de ⇒: p ⇒ q ≡ p ∨ q ≡ q
-- ------------------------------
-- Regla1: (p ⇒ q ≡ p ∨ q) ≡ q
implRule1 :: Rule
implRule1 = Rule { lhs = equiv (impl varP varQ) (or varP varQ)
                 , rhs = varQ
                 , rel = relEquiv
                 , name = pack ""
                 , desc = pack ""
                 }
                 
-- Regla2: p ⇒ q ≡ (p ∨ q ≡ q)
implRule2 :: Rule
implRule2 = Rule { lhs = impl varP varQ
                 , rhs = equiv (or varP varQ) varQ
                 , rel = relEquiv
                 , name = pack ""
                 , desc = pack ""
                 }
                 
-- ===========
-- CONSECUENCIA
-- ===========

-- ------------------------------
-- Definicion de ⇐: p ⇐ q ≡ p ∨ q ≡ p
-- ------------------------------
-- Regla1; (p ⇐ q ≡ p ∨ q) ≡ p
conseqRule1 :: Rule
conseqRule1 = Rule { lhs = equiv (conseq varP varQ) (or varP varQ)
                   , rhs = varP
                   , rel = relEquiv
                   , name = pack ""
                   , desc = pack ""
                   }
                   
-- Regla2: p ⇐ q ≡ (p ∨ q ≡ p)
conseqRule2 :: Rule
conseqRule2 = Rule { lhs = conseq varP varQ
                   , rhs = equiv (or varP varQ) varP
                   , rel = relEquiv
                   , name = pack ""
                   , desc = pack ""
                   }

-- AXIOMAS PARA LOS CUANTIFICADORES

-- ===========
-- PARA TODO
-- ===========

-- ------------------------------
-- Intercambio entre rango y término: <∀x : r.x : f.x> ≡ <∀x : : r.x ⇒ f.x>
-- ------------------------------

interRangeTermForall_Rule :: Rule
interRangeTermForall_Rule = Rule { lhs = forAll varX range term
                                 , rhs = forAll varX true $ impl range term
                                 , rel = relEquiv
                                 , name = pack ""
                                 , desc = pack ""
                                 }
    where varX = var "x" $ tyVar "A"
          range = Expr $ Var $ var "r" $ tyBool
          term = Expr $ Var $ var "t" $ tyBool
          
-- Axioma 5.3 (distributividad con or): X ∨ ∀x : : f.x ≡ ∀x : : X ∨ f.x , siempre que x no ocurra en X. 
-- DUDA: Cómo se implementa eso?

-- ------------------------------
-- Distributividad con ∧: <∀x : : f.x> ∧ <∀x : : g.x> ≡ <∀x : : f.x ∧ g.x>
-- ------------------------------
distribAndForall_Rule :: Rule
distribAndForall_Rule = Rule { lhs = and (forAll varX true term1) (forAll varX true term2)
                             , rhs = forAll varX true (and term1 term2)
                             , rel = relEquiv
                             , name = pack ""
                             , desc = pack ""
                             }
    where varX = var "x" $ tyVar "A"
          term1 = Expr $ Var $ var "t1" $ tyBool
          term2 = Expr $ Var $ var "t2" $ tyBool
                             
-- ------------------------------
-- Rango Unitario: <∀x : x = Y : f.x> ≡ f.Y
-- DUDA: Para definir esto tendriamos que saber si el tipo de la variable x tiene definida la igualdad. 
--       Algo como las typeclasses de haskell donde digamos que el tipo A es instancia de Eq, o algo así.
-- ------------------------------
-- unitRangeForall_Rule :: Rule
-- unitRangeForall_Rule = Rule { lhs = forAll (

-- ------------------------------
-- Intercambio de ∀: <∀x : : <∀y : : f.x.y> ≡ <∀y : : <∀x : : f.x.y>
-- DUDA: Es necesario que el termino sea una funcion que toma x e y? No podria ser cualquier termino?
-- ------------------------------
intercForall_Rule :: Rule
intercForall_Rule = Rule { lhs = forAll varX true $ forAll varY true term
                         , rhs = forAll varY true $ forAll varX true term
                         , rel = relEquiv
                         , name = pack ""
                         , desc = pack ""
                         }
    where varX = var "x" $ tyVar "A"
          varY = var "y" $ tyVar "A"
          term = Expr $ Var $ var "t" $ tyBool   


-- =======
-- EXISTE
-- =======

-- ------------------------------
-- Definicion de Existe: <∃x : r.x : f.x> ≡ ¬ <∀x : r.x : ¬f.x>
-- ------------------------------
existRule :: Rule
existRule = Rule { lhs = exist varX range term
                 , rhs = neg $ forAll varX range (neg term)
                 , rel = relEquiv
                 , name = pack ""
                 , desc = pack ""
                 }
    where varX = var "x" $ tyVar "A"
          range = Expr $ Var $ var "r" $ tyBool
          term = Expr $ Var $ var "t" $ tyBool
