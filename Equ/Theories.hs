-- | En este m&#243;dulo se re-exportan las definiciones sintácticas
-- de cada teoría y las reglas de reescritura de expresiones que
-- incluyen elementos sintácticos definidos en esa teoría.
{-# Language OverloadedStrings, TypeSynonymInstances #-}
module Equ.Theories 
    ( -- * Teor&#237;as.
      operatorsList
    , constantsList
    , quantifiersList
    , axiomList
    , axiomGroup
    , relationList
    , relToOp
    , createTheorem
    , theoremAddProof
    , createHypothesis
    , toForest
    , Grouped
    , TheoryName
    , theories
    , theoriesInGroup
    , arithAxioms
    , folAxioms
    , listAxioms
    , isTrue
    , isFalse
    )
    where

import Equ.Theories.AbsName
import Equ.Theories.Common (isTrue,isFalse)
import qualified Equ.Theories.Arith as A
import qualified Equ.Theories.List as L
import qualified Equ.Theories.FOL as F
import Equ.Rule(mkrule,Relation(..), Rule(..),relImpl,relEquiv,relCons,relEq)
import Equ.Proof.Proof
import Equ.Expr
import Equ.PreExpr

import Data.Text hiding (head,zip,concatMap,map,tail)
import Data.Maybe(isJust,fromJust)
import Data.Tree
import Control.Monad
import Control.Arrow ((&&&))

type TheoryName = Text

type Grouped a = [(TheoryName,[a])]

folTheory :: TheoryName
folTheory = "Proposicional"

arithTheory :: TheoryName
arithTheory = "Aritmética"

listTheory :: TheoryName
listTheory = "Listas"

theories :: [TheoryName]
theories = [folTheory,arithTheory,listTheory]

theoriesInGroup :: Grouped a -> [TheoryName]
theoriesInGroup = map fst

mkGrouped :: [TheoryName] -> [[a]] -> Grouped a
mkGrouped = zip

ungroup :: Grouped a -> [a]
ungroup = concatMap snd

toForest :: (TheoryName -> b) -> (a -> b) -> Grouped a -> Forest b
toForest fn fa = map (\(t,as) -> Node (fn t) (map (\x -> Node (fa x) []) as))

opGroup :: Grouped Operator
opGroup = mkGrouped theories [F.theoryOperatorsList, A.theoryOperatorsList, L.theoryOperatorsList]

constGroup :: Grouped Constant
constGroup = mkGrouped theories [F.theoryConstantsList, A.theoryConstantsList, L.theoryConstantsList]


mkAxiomGroup :: [[(Text,Expr,[Condition])]] -> Grouped Axiom
mkAxiomGroup axioms = mkGrouped theories . uncurry (:) . ((F.assocEquivAx:) . head &&& tail) $
                      map (map (uncurry2 createAxiom)) axioms

axiomGroup :: Grouped Axiom
axiomGroup = mkGrouped theories . uncurry (:) . ((F.assocEquivAx:) . head &&& tail) $
             map (map (uncurry2 createAxiom))
                     [ F.theoryAxiomList
                     , A.theoryAxiomList
                     , L.theoryAxiomList]
                     
     
arithAxioms,listAxioms,folAxioms :: [Axiom]                                     
arithAxioms = ungroup $ mkAxiomGroup [A.theoryAxiomList]
listAxioms = ungroup $ mkAxiomGroup [L.theoryAxiomList]
folAxioms = ungroup $ mkAxiomGroup [L.theoryAxiomList]
                     

operatorsList :: [Operator]
operatorsList = ungroup opGroup

constantsList :: [Constant]
constantsList = ungroup constGroup


axiomList :: [Axiom]
axiomList = ungroup axiomGroup

quantifiersList :: [Quantifier]
quantifiersList = A.theoryQuantifiersList ++ L.theoryQuantifiersList ++ F.theoryQuantifiersList

relationList :: [Relation]
relationList = [relEq,relEquiv,relImpl,relCons]



relToOp :: Relation -> Operator
relToOp relation | relation == relEq = F.folEqual
                 | relation == relEquiv = F.folEquiv
                 | relation == relImpl = F.folImpl
                 | relation == relCons = F.folConseq
relToOp _ = error "relToOp: Unknown relation!"

opToRel :: Operator -> Maybe Relation
opToRel op = case opName op of 
               Equival -> Just relEquiv
               Implic -> Just relImpl
               Conseq -> Just relCons
               Equal  -> Just relEq
               _ -> Nothing


getRelExp :: PreExpr -> Maybe Relation
getRelExp (BinOp op _ _) = opToRel op
getRelExp _ = Nothing


-- DUDA: VER SI ESTAS FUNCIONES QUE SIGUEN DEBEN IR EN ESTE MODULO O EN OTRO.
-- LAS QUISE PONER EN Equ.Proof PERO TENEMOS PROBLEMAS CON LOS IMPORTS


-- Funcion que dada una prueba y un nombre, crea un teorema:
-- Asume que la prueba tiene expresión inicial, final y relacion.

createTheorem :: Text -> Proof -> Theorem
createTheorem th_name proof = Theorem {
      thName = th_name
    , thExpr = Expr $ BinOp (relToOp rel') exp1 exp2
    , thRel = fromJust $ getRel proof
    , thProof = proof
    , thRules = createRulesAssoc expr
    , thCondition = []
    }
    
    where exp1 = (toExpr $ fromJust $ getStart proof)
          exp2 = (toExpr $ fromJust $ getEnd proof)          
          rel' = fromJust $ getRel proof
          expr = BinOp (relToOp rel') exp1 exp2
          
theoremAddProof :: Proof -> Theorem -> Theorem
theoremAddProof p t = t {thProof = p}
     
-- | Siempre que tenemos un axioma, tenemos dos reglas: @e ≡ True@ y @True ≡ e@.
metaRules :: Expr -> [Rule]
metaRules e = [ mkrule e F.true relEquiv, mkrule F.true e relEquiv]

-- | Dada una expresión, genera todas las reglas posibles de partir
-- esa expresión. 
createRulesAssoc :: PreExpr -> [Rule]
createRulesAssoc e = whenZ isJust rules (getRelExp e) ++ metaRules (Expr e)
    where rules (Just rel') = createPairs e >>= 
                             if relSym rel'
                             then \(p,q) -> [mkrule (Expr p) (Expr q) rel', mkrule (Expr q) (Expr p) rel']
                             else \(p,q) -> return (mkrule (Expr p) (Expr q) rel')
          rules _ = []
          

-- | Dado un axioma reconstruye las reglas a partir de su expresión.
createAxiom :: Text -> Expr -> [Condition] -> Axiom
createAxiom name' ex conditions = Axiom { 
                        axName = name'
                      , axExpr = ex
                      , axRel = fromJust $ getRelExp expr
                      , axRules = createRulesAssoc expr
                      , axCondition = conditions
                    } 
    where (Expr expr) = ex
          
          
-- | Dada una expresion, construye una hipotesis, calculando todas las reglas.
createHypothesis :: Text -> Expr -> [Condition] -> Hypothesis
createHypothesis name' ex@(Expr pe) conditions = Hypothesis { 
                        hypName = name'
                      , hypExpr = ex
                      , hypRel = fromJust $ getRelExp pe
                      , hypRule = createRulesAssoc pe
                      , hypCondition = conditions
                    } 

whenZ :: MonadPlus m => (a -> Bool) -> (a -> m b) -> a -> m b
whenZ p act a = if p a then act a else mzero
                                     
uncurry2 :: (a -> b -> c -> d) -> (a,b,c) -> d
uncurry2 f (a,b,c) = f a b c
                                     

                                     
                                     