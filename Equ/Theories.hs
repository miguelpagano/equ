-- | En este m&#243;dulo se re-exportan las definiciones sintácticas
-- de cada teoría y las reglas de reescritura de expresiones que
-- incluyen elementos sintácticos definidos en esa teoría.
{-# Language OverloadedStrings #-}
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
    , toForest
    , Grouped
    )
    where

import Equ.Theories.AbsName
import qualified Equ.Theories.Arith as A
import qualified Equ.Theories.List as L
import qualified Equ.Theories.FOL as F
import Equ.Rule
import Equ.Syntax (Operator,Constant,Quantifier)
import Equ.Proof
import Equ.Expr
import Equ.PreExpr

import Data.Text hiding (head,zip,concatMap,map)
import Data.Either(rights)
import Data.Maybe(isJust,fromJust)
import Data.Tree
import qualified Data.Foldable as DF  (mapM_) 
import Control.Monad

type TheoryName = Text
type Grouped a = [(TheoryName,[a])]

folTheory :: TheoryName
folTheory = "Proposicional"

arithTheory :: TheoryName
arithTheory = "Aritmética"

listTheory :: TheoryName
listTheory = "Listas"

theories = [folTheory,arithTheory,listTheory]

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

axiomGroup :: Grouped Axiom
axiomGroup = mkGrouped theories $ map (map (uncurry createAxiom)) 
                                [ F.theoryAxiomList
                                , A.theoryAxiomList
                                , L.theoryAxiomList]

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
    , thExpr = Expr $ BinOp (relToOp rel) exp1 exp2
    , thRel = fromRight $ getRel proof
    , thProof = proof
    , thRules = createRules exp1 exp2 rel
    }
    
    where exp1 = (toExpr $ fromRight $ getStart proof)
          exp2 = (toExpr $ fromRight $ getEnd proof)          
          fromRight = head . rights . return
          rel = fromRight $ getRel proof
     
createRules :: PreExpr -> PreExpr -> Relation -> [Rule]
createRules pe1 pe2 rel = (mkrule (Expr pe1) (Expr pe2) rel):metaRules expr
    where expr = Expr $ BinOp (relToOp rel) pe1 pe2

-- | Siempre que tenemos un axioma, tenemos dos reglas: @e ≡ True@ y @True ≡ e@.
metaRules :: Expr -> [Rule]
metaRules e = [ mkrule e F.true relEquiv, mkrule F.true e relEquiv]

-- | Dada una expresión, genera todas las reglas posibles de partir
-- esa expresión. 
createRulesAssoc :: PreExpr -> [Rule]
createRulesAssoc e = whenZ isJust rules (getRelExp e) ++ metaRules (Expr e)
    where rules (Just rel) = createPairs e >>= 
                             if relSym rel
                             then \(p,q) -> [mkrule (Expr p) (Expr q) rel, mkrule (Expr q) (Expr p) rel]
                             else \(p,q) -> return (mkrule (Expr p) (Expr q) rel)
          rules _ = []
          

-- | Dado un axioma reconstruye las reglas a partir de su expresión.
createAxiom :: Text -> Expr -> Axiom
createAxiom name ex = Axiom { 
                        axName = name
                      , axExpr = ex
                      , axRel = fromJust $ getRelExp expr
                      , axRules = createRulesAssoc expr} 
    where (Expr expr) = ex

whenZ :: MonadPlus m => (a -> Bool) -> (a -> m b) -> a -> m b
whenZ p act a = if p a then act a else mzero

