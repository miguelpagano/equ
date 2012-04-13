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
    , assocEquivAx
    , theoryAxiomList
    -- * Versión tipada de operadores.
    , true, false, equal, equiv, discrep
    , neg, and, or, impl, conseq, forAll, exist
    -- ** Cuantificador \"Existe\"
    -- *** Definicion
    )
    where

import Prelude hiding (and,or) 
import Equ.Syntax
import Equ.Types
import Equ.Expr
import Equ.PreExpr
import Equ.Rule
import Equ.Proof
import Equ.Theories.AbsName
import Equ.Theories.Common

import Data.Text(Text)

-- CONSTANTES
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

theoryAxiomList :: [(Text,Expr)]
theoryAxiomList = [ conmEquivAxiom
                  , trueLNeutralEquiv
                  , trueRNeutralEquiv
                  , negEquivAxiom
                  , falseDefAxiom
                  , discrepDefAxiom
                  , assocOrAxiom
                  , commOrAxiom
                  , idempotOrAxiom
                  , distEqOrAxiom
                  , excludThirdAxiom
                  , goldenRuleAxiom]

-- A continuacion definimos constructores de expresiones, para su facil manejo

-- | Constructores de Operaciones l&#243;gicas


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

-- assocEquivAx :: (Text,Expr)
-- assocEquivAx = ("Asociatividad de la Equivalencia", 
--                 associativityEquiv equiv varP varQ varR)


-- | Asociatividad de la equivalencia; este axioma no puede
-- generarse de la misma manera que los demás.
assocEquivAx = Axiom {  axName = "Asociatividad de la Equivalencia"
                      , axExpr = expr
                      , axRel = relEquiv
                      , axRules = map mkr [(lhs,rhs),(rhs,lhs),(expr,true),(true,expr)]
                     }
    where lhs = (varP `equiv` varR) `equiv` varQ
          rhs = varP `equiv` (varR `equiv` varQ)
          mkr (l,r) = mkrule l r relEquiv
          expr = associativityEquiv equiv varP varQ varR

-- Axioma Conmutatividad de la equivalencia:
conmEquivAxiom :: (Text,Expr)
conmEquivAxiom = ("Conmutatividad de la Equivalencia", 
                  symmetryEquiv equiv varP varQ)

trueLNeutralEquiv :: (Text,Expr)
trueLNeutralEquiv = ("Neutro de la equivalencia a izquierda", 
                     leftNeutralEquiv equiv true varP)

trueRNeutralEquiv :: (Text,Expr)
trueRNeutralEquiv = ("Neutro de la equivalencia a derecha", 
                     rightNeutralEquiv equiv true varP)


-- =========
-- NEGACION
-- =========

negEquivAxiom :: (Text,Expr)
negEquivAxiom = ("Negación y Equivalencia", 
                 neg (varP `equiv` varQ) `equiv` ((neg varP) `equiv` varQ))

{- | Definicion de false:
@
    False &#8801; &#172;True
@
-}
falseDefAxiom :: (Text,Expr)
falseDefAxiom = ("Definición de False",false `equiv` neg true)
                  

-- ============
-- DISCREPANCIA
-- ============

{- | Definicion de discrepancia:
@
    (p /&#8801; q) &#8801; &#172;(p &#8801; q)
@
-}
discrepDefAxiom :: (Text,Expr)
discrepDefAxiom = ("Definición de discrepancia",  
                   (discrep varP varQ) `equiv` (neg (equiv varP varQ)))
                    
-- ===========
-- DISYUNCION
-- ===========

{- | Regla asociatividad:
@
    (p &#8744; q) &#8744; r &#8801; p &#8744; (q &#8744; r)
@
-}
assocOrAxiom :: (Text,Expr)
assocOrAxiom = ("Asociatividad del ∨", 
                associativityEquiv or varP varR varQ)
                    
{- | Regla conmutatividad:
@
    p &#8744; q &#8801; q &#8744; p
@
-}
                  
commOrAxiom :: (Text,Expr)
commOrAxiom = ("Conmutatividad del ∨", symmetryEquiv or varP varQ)

{- | Regla idempotencia:
@
    p &#8744; p &#8801; p
@
-}

idempotOrAxiom :: (Text,Expr)
idempotOrAxiom = ("Idempotencia del ∨", varP `or` varP `equiv` varP)

                      
distEqOrAxiom :: (Text,Expr)
distEqOrAxiom = ("Distributividad de ≡ con ∨"
                , equiv (or varP (equiv varQ varR)) (equiv (or varP varQ) (or varP varR)))


{- | Tercero Excluido:
@
    p &#8744; &#172;p
@
-}
excludThirdAxiom :: (Text,Expr)
excludThirdAxiom = ("Tercero excluido", equiv (or varP (neg varP)) true)

-- ===========
-- CONJUNCION
-- ===========

goldenRuleAxiom :: (Text,Expr)
goldenRuleAxiom = ( "Regla Dorada"
                  , ((varP `and` varQ)  `equiv` varP) `equiv` (varQ `equiv` (varP `or` varQ))
                  )

                   
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
-- TODO!!

-- AXIOMAS PARA LOS CUANTIFICADORES

-- ===========
-- PARA TODO
-- ===========

{- | Intercambio entre rango y t&#233;rmino: 
@
    <&#8704;x : r.x : f.x> &#8801; <&#8704;x : : r.x &#8658; f.x>
@
-}
-- interRangeTermForall_Rule :: Rule
-- interRangeTermForall_Rule = Rule { lhs = forAll varX range term
--                                  , rhs = forAll varX true $ impl range term
--                                  , rel = relEquiv
--                                  , name = ""
--                                  , desc = ""
--                                  }
--     where varX = var "x" $ tyVar "A"
--           range = Expr $ Var $ var "r" $ tyBool
--           term = Expr $ Var $ var "t" $ tyBool
          
-- Axioma 5.3 (distributividad con or): X &#8744; &#8704;x : : f.x &#8801; &#8704;x : : X &#8744; f.x , siempre que x no ocurra en X. 
-- DUDA: C&#243;mo se implementa eso?

{- | Distributividad con &#8743;:
@
    <&#8704;x : : f.x> &#8743; <&#8704;x : : g.x> &#8801; <&#8704;x : : f.x &#8743; g.x>
@
-}
-- distribAndForall_Rule :: Rule
-- distribAndForall_Rule = Rule { lhs = and (forAll varX true term1) (forAll varX true term2)
--                              , rhs = forAll varX true (and term1 term2)
--                              , rel = relEquiv
--                              , name = ""
--                              , desc = ""
--                              }
--     where varX = var "x" $ tyVar "A"
--           term1 = Expr $ Var $ var "t1" $ tyBool
--           term2 = Expr $ Var $ var "t2" $ tyBool

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
-- intercForall_Rule :: Rule
-- intercForall_Rule = Rule { lhs = forAll varX true $ forAll varY true term
--                          , rhs = forAll varY true $ forAll varX true term
--                          , rel = relEquiv
--                          , name = ""
--                          , desc = ""
--                          }
--     where varX = var "x" $ tyVar "A"
--           varY = var "y" $ tyVar "A"
--           term = Expr $ Var $ var "t" $ tyBool   

-- =======
-- EXISTE
-- =======

-- {- | Definicion de Existe:
-- @
--     <&#8707;x : r.x : f.x> &#8801; &#172; <&#8704;x : r.x : &#172;f.x>
-- @
-- -}
-- existRule :: Rule
-- existRule = Rule { lhs = exist varX range term
--                  , rhs = neg $ forAll varX range (neg term)
--                  , rel = relEquiv
--                  , name = ""
--                  , desc = ""
--                  }
--     where varX = var "x" $ tyVar "A"
--           range = Expr $ Var $ var "r" $ tyBool
--           term = Expr $ Var $ var "t" $ tyBool



