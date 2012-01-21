-- | El m&#243;dulo de expresiones de f&#243;rmulas de primer orden.
{-# Language OverloadedStrings #-}
module Equ.Theories.FOL 
    ( -- * Constructores y operadores.
      folTrue , folFalse , folForall , folExist , folEqual
    , folEquiv, folDiscrep, folAnd, folOr, folNeg, folImpl, folConseq
    -- ** Listas de constructores y operadores
    , theoryConstantsList
    , theoryOperatorsList
    , theoryQuantifiersList
    -- ** Lista de axiomas de la teoria
    , theoryAxiomList
    -- * Versión tipada de operadores.
    , true, false, equal, equiv, discrep
    , neg, and, or, impl, conseq, forAll, exist
    -- * Reglas de la teoría.
    , folRules
    -- ** Conmutatividad.
    , conmEquiv_Rule1, conmEquiv_Rule2, conmEquiv_Rule3
    -- ** Neutro.
    , neuterEquiv_Rule1, neuterEquiv_Rule2
    -- ** Negacion.
    , equivNeg_Rule1, equivNeg_Rule2
    -- ** False.
    , false_Rule
    -- ** Discrepancia.
    , discrep_Rule
    -- ** Disyuncion
    -- *** Asociatividad.
    , asocOr_Rule
    -- *** Conmutatividad.
    , conmOr_Rule
    -- *** Idempotencia.
    , idempotOr_Rule, idempotOr_Rule1
    -- *** Distributividad.
    , distEqOr_Rule1, distEqOr_Rule2
    -- *** Tercero excluido.
    , excludOr_Rule
    -- ** Conjuncion.
    , goldenRule1, goldenRule2
    , goldenRule3, goldenRule4, goldenRule5
    -- ** Implicacion.
    , implRule1, implRule2
    -- ** Consecuencia.
    , conseqRule1, conseqRule2
    -- ** Cuantificador \"Para todo\"
    -- *** Intercambio entre rango y termino.
    , interRangeTermForall_Rule
    -- *** Distributividad.
    , distribAndForall_Rule
    -- *** Intercambio de ∀
    , intercForall_Rule
    -- ** Cuantificador \"Existe\"
    -- *** Definicion
    , existRule
    , addBoolHypothesis
    )
    where

import Prelude hiding (and,or) 
import Equ.Syntax
import Equ.Types
import Equ.Expr
import Equ.PreExpr
import Equ.Rule
import Equ.Theories.AbsName
import Equ.Proof


-- CONSTANTES

-- | Constante True
folTrue :: Constant
folTrue = Constant { conRepr = "True"
                   , conName = CTrue
                   , conTy = tyBool
                   }

-- | Constante False  
folFalse :: Constant          
folFalse = Constant { conRepr = "False"
                    , conName = CFalse
                    , conTy = tyBool
                    }
                     
-- CUANTIFICADORES
-- | Cuantificador &#8704;
folForall :: Quantifier
folForall = Quantifier { quantRepr = "∀"
                       , quantName = Forall
                       , quantTy = tyVar "A" :-> tyBool
                       }

-- | Cuantificador &#8707;
folExist :: Quantifier
folExist = Quantifier { quantRepr = "∃"
                      , quantName = Exist
                      , quantTy = tyVar "A" :-> tyBool
                      }

-- OPERACIONES

-- Tipo de las operaciones logicas
folUnOpType,folBinOpType :: Type
folUnOpType = tyBool :-> tyBool
folBinOpType = tyBool :-> tyBool :-> tyBool

-- | Igualdad =
folEqual :: Operator
folEqual = Operator { opRepr = "="
                  , opName = Equal
                  , opTy = tyVar "A" :-> tyVar "A" :-> tyBool
                  , opAssoc = ALeft
                  , opNotationTy = NInfix
                  , opPrec = 5
                  }

-- | Equivalencia &#8801;
folEquiv :: Operator
folEquiv = Operator { opRepr = "≡"
                    , opName = Equival
                    , opTy = folBinOpType
                    , opAssoc = ALeft
                    , opNotationTy = NInfix
                    , opPrec = 1
                    }
                    
-- | Discrepancia /&#8801;
folDiscrep :: Operator
folDiscrep = Operator { opRepr = "/≡"
                      , opName = Discrep
                      , opTy = folBinOpType
                      , opAssoc = ALeft
                      , opNotationTy = NInfix
                      , opPrec = 1
                      }

-- | Conjuncion &#8743;
folAnd :: Operator
folAnd = Operator { opRepr = "∧"
                  , opName = And
                  , opTy = folBinOpType
                  , opAssoc = ALeft
                  , opNotationTy = NInfix
                  , opPrec = 3
                  }

-- | Disyuncion &#8744;
folOr :: Operator
folOr = Operator { opRepr = "∨"
                 , opName = Or
                 , opTy = folBinOpType
                 , opAssoc = ALeft
                 , opNotationTy = NInfix
                 , opPrec = 3
                 }
     
-- | Negacion &#172;
folNeg :: Operator
folNeg = Operator { opRepr = "¬"
                  , opName = Neg
                  , opTy = folUnOpType
                  , opAssoc = None
                  , opNotationTy = NPrefix
                  , opPrec = 4
                  }

-- | Implicaci&#243;n &#8658;
folImpl :: Operator
folImpl = Operator { opRepr = "⇒"
                   , opName = Implic
                   , opTy = folBinOpType
                   , opAssoc = ARight
                   , opNotationTy = NInfix
                   , opPrec = 2
                   }

-- | Consecuencia &#8656;
folConseq :: Operator
folConseq = Operator { opRepr = "⇐"
                     , opName = Conseq
                     , opTy = folBinOpType
                     , opAssoc = ALeft
                     , opNotationTy = NInfix
                     , opPrec = 2
                     }

-- | Constantes de FOL.
theoryConstantsList :: [Constant]
theoryConstantsList = [folTrue,folFalse]

-- | Operadores de FOL.
theoryOperatorsList :: [Operator]
theoryOperatorsList = [folEqual,folEquiv,folDiscrep,folAnd,folOr,folImpl,folConseq,folNeg]

-- | Cuantificadores de FOL.
theoryQuantifiersList :: [Quantifier]
theoryQuantifiersList = [folForall,folExist]

theoryAxiomList :: [Axiom]
theoryAxiomList = [conmEquivAxiom,neuterEquivAxiom,equivNegAxiom,falseDefAxiom,
                   discrepDefAxiom,asocOrAxiom,conmOrAxiom,idempotOrAxiom,distEqOrAxiom,
                   excludThirdAxiom,goldenRuleAxiom]

-- A continuacion definimos constructores de expresiones, para su facil manejo

-- | Constructor de Constantes logicas
true :: Expr
true = Expr $ Con $ folTrue

false :: Expr
false = Expr $ Con $ folFalse

-- | Constructores de Operaciones l&#243;gicas

-- | Igualdad
equal :: Expr -> Expr -> Expr
equal (Expr a) (Expr b) = Expr $ BinOp folEqual a b

-- | Equivalencia
equiv :: Expr -> Expr -> Expr
equiv (Expr p) (Expr q) = Expr $ BinOp folEquiv p q

-- | Discrepancia
discrep :: Expr -> Expr -> Expr
discrep (Expr p) (Expr q) = Expr $ BinOp folDiscrep p q

-- | Negacion
neg :: Expr -> Expr
neg (Expr p) = Expr $ UnOp folNeg p

-- | And
and :: Expr -> Expr -> Expr
and (Expr p) (Expr q) = Expr $ BinOp folAnd p q

-- | Or
or :: Expr -> Expr -> Expr
or (Expr p) (Expr q) = Expr $ BinOp folOr p q

-- | Implicacion
impl :: Expr -> Expr -> Expr
impl (Expr p) (Expr q) = Expr $ BinOp folImpl p q

-- | Consecuencia
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
varP,varQ,varR :: Expr
varP= Expr $ Var $ var "p" tyBool
varQ= Expr $ Var $ var "q" tyBool
varR= Expr $ Var $ var "r" tyBool

-- ============
-- EQUIVALENCIA
-- ============

-- Ascociatividad: ((p &#8801; q) &#8801; r) &#8801; (p &#8801; (q &#8801; r))
-- VER CUANTAS SON LAS REGLAS QUE HAY QUE HACER PARA ESTE AXIOMA.
-- Aca hay solo dos opciones, el equivalente del medio es siempre el de "relacion".
-- Las dos formas posibles son conmutar ambos miembros.

exprAsocEquiv :: Expr
exprAsocEquiv = equiv (equiv (equiv varP varQ) varR) (equiv varP (equiv varQ varR))

-- ---------------------------------
-- Conmutatividad: p &#8801; q &#8801; q &#8801; p
-- ---------------------------------
{- | Regla 1:
@
    p &#8801; (q &#8801; (q &#8801; p))
@
-}
conmEquiv_Rule1 :: Rule
conmEquiv_Rule1 = Rule { lhs = varP
                  , rhs = equiv varQ (equiv varQ varP)
                  , rel = relEquiv
                  , name = ""
                  , desc = ""
                  }
 
{- | Regla 2:
@
    (p &#8801; q) &#8801; (q &#8801; p)
@
-}
conmEquiv_Rule2 :: Rule
conmEquiv_Rule2 = Rule { lhs = equiv varP varQ
                       , rhs = equiv varQ varP
                       , rel = relEquiv
                       , name = ""
                       , desc = ""
                       }

{- | Regla 3:
@
    ((p &#8801; q) &#8801; q) &#8801; p
@
-}
conmEquiv_Rule3 :: Rule
conmEquiv_Rule3 = Rule { lhs = equiv (equiv varP varQ) varQ
                       , rhs = varP
                       , rel = relEquiv
                       , name = ""
                       , desc = ""
                       }

-- Axioma Conmutatividad de la equivalencia:
conmEquivAxiom :: Axiom
conmEquivAxiom = Axiom { axName = "Conmutatividad de la Equivalencia"
                       , axExpr = equiv (equiv varP varQ) (equiv varQ varP)
                       , axRel = relEquiv
                       , axRules = [conmEquiv_Rule1,conmEquiv_Rule2,conmEquiv_Rule3]
                       }

-- NOTA: No se si hace falta poner dos reglas mas, que serian:
-- (p &#8801; (q &#8801; q)) &#8801; p
-- p &#8801; ((q &#8801; q) &#8801; p)
-- Puesto que q &#8801; q es True por Neutro de Equiv

-- ------------------------------
-- Neutro: p &#8801; True &#8801; p
-- ------------------------------
{- | Regla 1:
@
    (p &#8801; True) &#8801; p
@
-}
neuterEquiv_Rule1 :: Rule
neuterEquiv_Rule1 = Rule { lhs = equiv varP true
                         , rhs = varP
                         , rel = relEquiv
                         , name = ""
                         , desc = ""
                         }
                         
{- | Regla 2:
@
    p &#8801; (True &#8801; p)
@
-}
neuterEquiv_Rule2 :: Rule
neuterEquiv_Rule2 = Rule { lhs = varP
                         , rhs = equiv true varP
                         , rel = relEquiv
                         , name = ""
                         , desc = ""
                         }

-- Axioma Neutro de la equivalencia
neuterEquivAxiom :: Axiom
neuterEquivAxiom = Axiom { axName = "Neutro de la equivalencia"
                       , axExpr = equiv (equiv varP true) varP
                       , axRel = relEquiv
                       , axRules = [neuterEquiv_Rule1,neuterEquiv_Rule2]
                       }


-- =========
-- NEGACION
-- =========

-- ------------------------------
-- Negacion y Equivalencia: &#172;(p &#8801; q) &#8801; &#172;p &#8801; q
-- ------------------------------
{- | Regla 1:
@
    &#172;(p &#8801; q) &#8801; (&#172;p &#8801; q)
@
-}
equivNeg_Rule1 :: Rule
equivNeg_Rule1 = Rule { lhs = neg $ equiv varP varQ
                      , rhs = equiv (neg varP) varQ
                      , rel = relEquiv
                      , name = ""
                      , desc = ""
                      }
                      
{- | Regla 2:
@
    (&#172;(p &#8801; q) &#8801; &#172;p) &#8801; q
@
-}
equivNeg_Rule2 :: Rule
equivNeg_Rule2 = Rule { lhs = equiv (neg $ equiv varP varQ) (neg varP)
                      , rhs = varQ
                      , rel = relEquiv
                      , name = ""
                      , desc = ""
                      }
                      
-- Axioma Negación y Equivalencia
equivNegAxiom :: Axiom
equivNegAxiom = Axiom { axName = "Negación y Equivalencia"
                       , axExpr = equiv (neg $ equiv varP varQ) (equiv (neg varP) varQ)
                       , axRel = relEquiv
                       , axRules = [equivNeg_Rule1,equivNeg_Rule2]
                       }

{- | Definicion de false:
@
    False &#8801; &#172;True
@
-}
false_Rule :: Rule
false_Rule = Rule { lhs = false
                  , rhs = neg true
                  , rel = relEquiv
                  , name = ""
                  , desc = ""
                  }
                  
falseDefAxiom :: Axiom
falseDefAxiom = Axiom { axName = "Definición de False"
                      , axExpr = equiv false (neg true)
                      , axRel = relEquiv
                      , axRules = [false_Rule]
                      }

-- ============
-- DISCREPANCIA
-- ============

{- | Definicion de discrepancia:
@
    (p /&#8801; q) &#8801; &#172;(p &#8801; q)
@
-}
discrep_Rule :: Rule
discrep_Rule = Rule { lhs = discrep varP varQ
                    , rhs = neg $ equiv varP varQ
                    , rel = relEquiv
                    , name = ""
                    , desc = ""
                    }

discrepDefAxiom :: Axiom
discrepDefAxiom = Axiom { axName = "Definición de discrepancia"
                        , axExpr = equiv (discrep varP varQ) (neg (equiv varP varQ))
                        , axRel = relEquiv
                        , axRules = [discrep_Rule]
                    }
                    
-- ===========
-- DISYUNCION
-- ===========

{- | Regla asociatividad:
@
    (p &#8744; q) &#8744; r &#8801; p &#8744; (q &#8744; r)
@
-}
asocOr_Rule :: Rule
asocOr_Rule = Rule { lhs = or (or varP varQ) varR
                  , rhs = or varP (or varQ varR)
                  , rel = relEquiv
                  , name = ""
                  , desc = ""
                  }
                  
asocOrAxiom :: Axiom
asocOrAxiom = Axiom { axName = "Asociatividad del ∨"
                    , axExpr = equiv (or (or varP varQ) varR) (or varP (or varQ varR))
                    , axRel = relEquiv
                    , axRules = [asocOr_Rule]
                    }
                    
{- | Regla conmutatividad:
@
    p &#8744; q &#8801; q &#8744; p
@
-}
conmOr_Rule :: Rule
conmOr_Rule = Rule { lhs = or varP varQ
                  , rhs = or varQ varP
                  , rel = relEquiv
                  , name = ""
                  , desc = ""
                  }
                  
conmOrAxiom :: Axiom
conmOrAxiom = Axiom { axName = "Conmutatividad del ∨"
                    , axExpr = equiv (or varP varQ) (or varQ varP)
                    , axRel = relEquiv
                    , axRules = [conmOr_Rule]
                    }

{- | Regla idempotencia:
@
    p &#8744; p &#8801; p
@
-}
idempotOr_Rule :: Rule
idempotOr_Rule = Rule { lhs = or varP varP
                      , rhs = varP
                      , rel = relEquiv
                      , name = ""
                      , desc = ""
                      }

{- | Regla idempotencia:
@
    (p &#8744; p &#8801; p) &#8801; True
@
-}
idempotOr_Rule1 :: Rule
idempotOr_Rule1 = Rule { lhs = equiv (or varP varP) (varP)
                      , rhs = true
                      , rel = relEquiv
                      , name = ""
                      , desc = ""
                      }

idempotOrAxiom :: Axiom
idempotOrAxiom = Axiom { axName = "Idempotencia del ∨"
                        , axExpr = equiv (or varP varP) varP
                        , axRel = relEquiv
                        , axRules = [idempotOr_Rule,idempotOr_Rule1]
                        }

{- | Regla 1 distributividad con equivalencia: 
@
    p &#8744; (q &#8801; r) &#8801; ((p &#8744; q) &#8801; (p &#8744; r))
@
-}
distEqOr_Rule1 :: Rule
distEqOr_Rule1 = Rule { lhs = or varP $ equiv varQ varR
                      , rhs = equiv (or varP varQ) (or varP varR)
                      , rel = relEquiv
                      , name = ""
                      , desc = ""
                      }

{- | Regla 2 distributividad con equivalencia:
@
    (p &#8744; (q &#8801; r) &#8801; (p &#8744; q)) &#8801; (p &#8744; r)
@
-}
distEqOr_Rule2 :: Rule
distEqOr_Rule2 = Rule { lhs = equiv (or varP $ equiv varQ varR) (or varP varQ)
                      , rhs = or varP varR
                      , rel = relEquiv
                      , name = ""
                      , desc = ""
                      }
                      
distEqOrAxiom :: Axiom
distEqOrAxiom = Axiom { axName = "Distributividad de ≡ con ∨"
                      , axExpr = equiv (or varP (equiv varQ varR)) (equiv (or varP varQ) (or varP varR))
                      , axRel = relEquiv
                      , axRules = [distEqOr_Rule1,distEqOr_Rule2]
                      }

{- | Tercero Excluido:
@
    p &#8744; &#172;p
@
-}
excludOr_Rule :: Rule
excludOr_Rule = Rule { lhs = or varP $ neg varP
                     , rhs = true
                     , rel = relEquiv
                     , name = ""
                     , desc = ""
                     }
                     
excludThirdAxiom :: Axiom
excludThirdAxiom = Axiom { axName = "Tercero excluido"
                         , axExpr = or varP (neg varP)
                         , axRel = relEquiv
                         , axRules = [excludOr_Rule]
                         }

-- ===========
-- CONJUNCION
-- ===========

{- | Regla 1 regla dorada:
@
    p &#8743; q &#8801; (p &#8801; (q &#8801; p &#8744; q))
@
-}
goldenRule1 :: Rule
goldenRule1 = Rule { lhs = and varP varQ
                   , rhs = equiv varP $ equiv varQ $ or varP varQ
                   , rel = relEquiv
                   , name = ""
                   , desc = ""
                   }

{- | Regla 2 regla dorada:
@
    p &#8743; q &#8801; ((p &#8801; q) &#8801; p &#8744; q)
@
-}
goldenRule2 :: Rule
goldenRule2 = Rule { lhs = and varP varQ
                   , rhs = equiv (equiv varP varQ) (or varP varQ)
                   , rel = relEquiv
                   , name = ""
                   , desc = ""
                   }
                   
-- DUDA: Hace falta definir dos reglas para lo anterior? 
-- p &#8743; q &#8801; (p &#8801; q &#8801; p &#8744; q)
-- Si nosotros escribimos el lado derecho de una de las dos formas posibles, luego
-- la otra forma podria ser derivada por la regla de asociatividad:
-- p &#8801; (q &#8801; p &#8744; q) es equivalente a ((p &#8801; q) &#8801; p &#8744; q)


{- | Regla 3 regla dorada:
@
    ((p &#8743; q) &#8801; p) &#8801; (q &#8801; p &#8744; q)
@
-}
goldenRule3 :: Rule
goldenRule3 = Rule { lhs = equiv (and varP varQ) varP
                   , rhs = equiv varQ $ or varP varQ
                   , rel = relEquiv
                   , name = ""
                   , desc = ""
                   }


-- Tenemos la misma cuesti&#243;n sobre la asociatividad en las siguientes reglas
{- | Regla 4 regla dorada:
@
    (p &#8743; q &#8801; p) &#8801; q) &#8801; p &#8744; q
@
-}
goldenRule4 :: Rule
goldenRule4 = Rule { lhs = equiv (equiv (and varP varQ) varQ) (or varP varQ)
                   , rhs = or varP varQ
                   , rel = relEquiv
                   , name = ""
                   , desc = ""
                   }
                   

{- | Regla 5 regla dorada:
@
    (p &#8743; q &#8801; (p &#8801; q)) &#8801; p &#8744; q
@
-}
goldenRule5 :: Rule
goldenRule5 = Rule { lhs = equiv (and varP varQ) (equiv varP varQ)
                   , rhs = or varP varQ
                   , rel = relEquiv
                   , name = ""
                   , desc = ""
                   }

goldenRuleAxiom :: Axiom
goldenRuleAxiom = Axiom { axName = "Regla Dorada"
                        , axExpr = equiv (equiv (and varP varQ) varP) (equiv varQ (or varP varQ))
                        , axRel = relEquiv
                        , axRules = [goldenRule1,goldenRule2,goldenRule3,goldenRule4,goldenRule5]
                        }
                   
-- ===========
-- IMPLICACION
-- ===========

-- ------------------------------
-- Definicion de &#8658;: p &#8658; q &#8801; p &#8744; q &#8801; q
-- ------------------------------

{- | Regla 1 implicacion:
@
    (p &#8658; q &#8801; p &#8744; q) &#8801; q
@
-}
implRule1 :: Rule
implRule1 = Rule { lhs = equiv (impl varP varQ) (or varP varQ)
                 , rhs = varQ
                 , rel = relEquiv
                 , name = ""
                 , desc = ""
                 }

{- | Regla 2 implicacion:
@
    p &#8658; q &#8801; (p &#8744; q &#8801; q)
@
-}
implRule2 :: Rule
implRule2 = Rule { lhs = impl varP varQ
                 , rhs = equiv (or varP varQ) varQ
                 , rel = relEquiv
                 , name = ""
                 , desc = ""
                 }

-- ===========
-- CONSECUENCIA
-- ===========

-- ------------------------------
-- Definicion de &#8656;: p &#8656; q &#8801; p &#8744; q &#8801; p
-- ------------------------------
{- | Regla 1 consecuencia:
@
    (p &#8656; q &#8801; p &#8744; q) &#8801; p
@
-}
conseqRule1 :: Rule
conseqRule1 = Rule { lhs = equiv (conseq varP varQ) (or varP varQ)
                   , rhs = varP
                   , rel = relEquiv
                   , name = ""
                   , desc = ""
                   }

{- | Regla 2 consecuencia:
@
    p &#8656; q &#8801; (p &#8744; q &#8801; p)
@
-}
conseqRule2 :: Rule
conseqRule2 = Rule { lhs = conseq varP varQ
                   , rhs = equiv (or varP varQ) varP
                   , rel = relEquiv
                   , name = ""
                   , desc = ""
                   }

-- AXIOMAS PARA LOS CUANTIFICADORES

-- ===========
-- PARA TODO
-- ===========

{- | Intercambio entre rango y t&#233;rmino: 
@
    <&#8704;x : r.x : f.x> &#8801; <&#8704;x : : r.x &#8658; f.x>
@
-}
interRangeTermForall_Rule :: Rule
interRangeTermForall_Rule = Rule { lhs = forAll varX range term
                                 , rhs = forAll varX true $ impl range term
                                 , rel = relEquiv
                                 , name = ""
                                 , desc = ""
                                 }
    where varX = var "x" $ tyVar "A"
          range = Expr $ Var $ var "r" $ tyBool
          term = Expr $ Var $ var "t" $ tyBool
          
-- Axioma 5.3 (distributividad con or): X &#8744; &#8704;x : : f.x &#8801; &#8704;x : : X &#8744; f.x , siempre que x no ocurra en X. 
-- DUDA: C&#243;mo se implementa eso?

{- | Distributividad con &#8743;:
@
    <&#8704;x : : f.x> &#8743; <&#8704;x : : g.x> &#8801; <&#8704;x : : f.x &#8743; g.x>
@
-}
distribAndForall_Rule :: Rule
distribAndForall_Rule = Rule { lhs = and (forAll varX true term1) (forAll varX true term2)
                             , rhs = forAll varX true (and term1 term2)
                             , rel = relEquiv
                             , name = ""
                             , desc = ""
                             }
    where varX = var "x" $ tyVar "A"
          term1 = Expr $ Var $ var "t1" $ tyBool
          term2 = Expr $ Var $ var "t2" $ tyBool

-- ------------------------------
-- Rango Unitario: <&#8704;x : x = Y : f.x> &#8801; f.Y
-- DUDA: Para definir esto tendriamos que saber si el tipo de la variable x tiene definida la igualdad. 
--       Algo como las typeclasses de haskell donde digamos que el tipo A es instancia de Eq, o algo as&#237;.
-- ------------------------------
{-unitRangeForall_Rule :: Rule
unitRangeForall_Rule = Rule { lhs = forAll varX (equal expr_varX expr_varY) term
                            , rhs = Expr $ applySubst subst term
                            , rel = relEquiv
                            , name = ""
                            , desc = ""
                            }
    where varX = var "x" $ tyVar "A"
          varY = var "y" $ tyVar "A"
          expr_varX = Expr $ Var $ varX
          expr_varY = Expr $ Var $ varY
          term = Expr $ Var $ var "t" $ tyBool
          subst = M.insert varX (Expr varY) M.empty
          -}
-- ------------------------------
-- Intercambio de &#8704;: <&#8704;x : : <&#8704;y : : f.x.y> &#8801; <&#8704;y : : <&#8704;x : : f.x.y>
-- DUDA: Es necesario que el termino sea una funcion que toma x e y? No podria ser cualquier termino?
-- ------------------------------
{- | Intercambio de &#8704;:
@
    <&#8704;x : : <&#8704;y : : f.x.y> &#8801; <&#8704;y : : <&#8704;x : : f.x.y>
@
-}
intercForall_Rule :: Rule
intercForall_Rule = Rule { lhs = forAll varX true $ forAll varY true term
                         , rhs = forAll varY true $ forAll varX true term
                         , rel = relEquiv
                         , name = ""
                         , desc = ""
                         }
    where varX = var "x" $ tyVar "A"
          varY = var "y" $ tyVar "A"
          term = Expr $ Var $ var "t" $ tyBool   

-- =======
-- EXISTE
-- =======

{- | Definicion de Existe:
@
    <&#8707;x : r.x : f.x> &#8801; &#172; <&#8704;x : r.x : &#172;f.x>
@
-}
existRule :: Rule
existRule = Rule { lhs = exist varX range term
                 , rhs = neg $ forAll varX range (neg term)
                 , rel = relEquiv
                 , name = ""
                 , desc = ""
                 }
    where varX = var "x" $ tyVar "A"
          range = Expr $ Var $ var "r" $ tyBool
          term = Expr $ Var $ var "t" $ tyBool


folRules :: [Rule]
folRules = [ conmEquiv_Rule1, conmEquiv_Rule2, conmEquiv_Rule3 -- Conmutatividad.
           , neuterEquiv_Rule1, neuterEquiv_Rule2 -- Neutro.
           , equivNeg_Rule1, equivNeg_Rule2 -- Negacion.
           , false_Rule
           , discrep_Rule
           , asocOr_Rule
           , conmOr_Rule
           , idempotOr_Rule
           , distEqOr_Rule1, distEqOr_Rule2 -- Discrepancia.
           , excludOr_Rule
            --Regla dorada.
           , goldenRule1, goldenRule2, goldenRule3, goldenRule4, goldenRule5
           , implRule1, implRule2 -- Implicacion.
           , conseqRule1, conseqRule2 -- Consecuencia.
           , interRangeTermForall_Rule
           , distribAndForall_Rule
           , intercForall_Rule
           , existRule
           ]


addBoolHypothesis :: PreExpr -> Ctx -> (Ctx,Maybe Name)
addBoolHypothesis e = addHypothesis e relEquiv [Con folTrue]