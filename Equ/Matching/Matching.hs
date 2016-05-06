{- Algoritmo de Matching Asociativo Conmutativo. 
   Basado en el algoritmo eager del paper "Lazy AC-Pattern Matching for Rewriting",
   Belkhir y Giorgetti-}

module Equ.Matching.Matching where


import Equ.PreExpr hiding (rename)
import Equ.Theories.Common (folOr,folAnd,folEquiv)
import Equ.Matching.Monad
import Equ.Matching.Error
import Data.List (permutations)
import Math.Combinat.Partitions.Multiset (partitionMultiset)
import Control.Applicative ((<$>))
import Control.Monad (foldM)
import Control.Monad.Trans.State (runState)
import qualified Data.Map as M


{- Operadores asociativo/conmutativos -}
operatorListAC :: [Operator]
operatorListAC = [folOr,folAnd,folEquiv]

data MatchSubst = MatchSubst 
            { subst  :: FESubst
            , rename :: VariableRename
            }
    deriving Show
            
emptyMSubst :: MatchSubst
emptyMSubst = MatchSubst { subst = M.empty
                         , rename = M.empty
                         }

data MatchRes = Solution MatchSubst
              | MError [MatchInfo] MatchError
              
type MErrWInfo = ([MatchInfo],MatchError)
              
instance Show MatchRes where
    show (Solution ms)  = "Solution: " ++ (show ms)
    show (MError mi er) = unlines $ ["Error: " ++ show er, (unlines $ map show mi)]

type FESubst = M.Map Variable FlatExpr

type VariableRename = M.Map Variable Variable
              
type Surj = [[Int]]
              
matcherr :: MatchError -> TMatch MatchRes
matcherr er = flip MError er <$>  getInfo

matchadd :: Variable -> FlatExpr -> MatchSubst -> TMatch MatchRes
matchadd v fe ms = return $ Solution (ms { subst  = M.insert v fe (subst ms) })

-- Todas las funciones suryectivas de un conjunto con n elementos
-- en uno con k elementos.
allSurjs :: Int -> Int -> [Surj]
allSurjs k n = concatMap permutations p
    where p = filter ((k==) . length) $ partitionMultiset [0..(n-1)]

whenM1 :: Bool -> MatchSubst -> MatchError -> TMatch [MatchRes]
whenM1 b ms er = if b then return [Solution ms]
                     else (: []) <$> matcherr er
                     
whenM :: Bool -> TMatch [MatchRes] -> MatchError -> TMatch [MatchRes]
whenM b res er = if b then res
                     else (: []) <$> matcherr er
            
takeIndices :: [a] -> [Int] -> [a]
takeIndices _ []      = []
takeIndices ls (i:is) = ls!!i : takeIndices ls is
    
    
-- PRE: length surj = k <= length fs
-- POST: k = length (applySurj op surj fs)
applySurj :: Operator -> Surj -> [FlatExpr] -> [FlatExpr]
applySurj op surj fs = map asoc surj
    where asoc :: [Int] -> FlatExpr
          asoc []          = error "Imposible: applySurj"
          asoc [i]         = fs!!i
          asoc is@(_:_:_) = FBin op $ takeIndices fs is
    
matchBin :: Operator -> [FlatExpr] -> [FlatExpr] -> MatchSubst -> TMatch [MatchRes]
matchBin op ps es ms = getOpsac >>= matchBin'
    where matchBin' oplist
            | op `elem` oplist = if k > n then (: []) <$> matcherr (SubTermsAC op ps es)
                                else foldM (\b surj -> (b ++) <$> 
                                            matchNoAC ps (applySurj op surj es)) 
                                            [] (allSurjs k n)
            | otherwise = matchNoAC ps es
                where k = length ps
                      n = length es
                      sol = Solution ms
                      matchNoAC ps' es' | length ps' == length es' = 
                                                foldM (\b (p,e) -> matchAC p e b)
                                                      [sol] (zip ps' es')
                                        | otherwise = (: []) <$> 
                                                    matcherr (NOperands op ps es)
            
matchingAC :: FlatExpr -> FlatExpr -> MatchSubst -> TMatch [MatchRes]
matchingAC p@(FVar v) fe ms = elemVar v >>= \b ->
    if b && p/=fe then (: []) <$> matcherr (BindingVar v)
                  else maybe ((: []) <$> matchadd v fe ms)
                             (\f -> whenM1 (fe == f) ms (DoubleMatch v f fe))
                             $ M.lookup v s
    where s = subst ms
matchingAC (FUn op p') (FUn o fe') ms = 
    whenM (op == o) (matchAC' p' fe' (Solution ms))
                    (InequOperator op o)
matchingAC (FBin op ps) (FBin o es) ms =
    whenM (op == o) (matchBin op ps es ms)
                    (InequOperator op o)
matchingAC (FQuant _ _ _ _) (FQuant _ _ _ _) _ = undefined
    --whenM (q == r) (matchQuant q v w p1 e1 p2 e2)
    --               (InequQuantifier q r)
matchingAC p e ms = whenM1 (p == e) ms (InequPreExpr p e)

    
matchAC' :: FlatExpr -> FlatExpr -> MatchRes -> TMatch [MatchRes]
matchAC' _ _ mr@(MError _ _) = return [mr]
matchAC' pat fe (Solution ms) = 
    pushInfo pat fe >> matchingAC pat fe ms >>= 
    \mrs -> popInfo >> return mrs

    
matchAC :: FlatExpr -> FlatExpr -> [MatchRes] -> TMatch [MatchRes]
matchAC pat fe mrs = foldM (\b res -> (b ++) <$> matchAC' pat fe res) [] mrs

match' :: PreExpr -> PreExpr -> [MatchRes] -> TMatch [MatchRes]
match' p e = matchAC (flat p) (flat e)

match :: [Operator] -> PreExpr -> PreExpr -> Either [MErrWInfo] MatchSubst
match opsac e e' = 
    let (mres,_) = runState (match' e e' [Solution emptyMSubst]) (initMSt opsac)
    in
        getMatchRes mres []
             
getMatchRes :: [MatchRes] -> [MErrWInfo] -> Either [MErrWInfo] MatchSubst
getMatchRes [] ers       = Left ers
getMatchRes (mr:mrs) ers = case mr of
                                Solution s -> Right s
                                MError mis me  -> getMatchRes mrs 
                                                    (ers ++ [(mis,me)])

