
module Equ.Matching.Monad where

import Equ.PreExpr
import Control.Monad.Trans.State
import Control.Applicative ((<$>)) 

data MatchInfo = MatchInfo 
            { patt :: FlatExpr
            , expr :: FlatExpr
            }

data MatchSt = MatchSt { minfo :: [MatchInfo]
                       , bvars :: [Variable]
                       , opsac :: [Operator]
                       }

type TMatch = State MatchSt

pushInfo :: FlatExpr -> FlatExpr -> TMatch ()
pushInfo fe fe' = modify (\mst -> mst { minfo = mi : minfo mst })
    where mi = MatchInfo { patt = fe
                         , expr = fe'
                         }
                    
popInfo :: TMatch ()
popInfo = modify (\mst -> mst { minfo = tail $ minfo mst} )

getInfo :: TMatch [MatchInfo]
getInfo = minfo <$> get

getOpsac :: TMatch [Operator]
getOpsac = opsac <$> get

addVar :: Variable -> TMatch ()
addVar v = modify (\mst -> mst { bvars = v : bvars mst })

elemVar :: Variable -> TMatch Bool
elemVar v = elem v . bvars <$> get

initMSt :: [Operator] -> MatchSt
initMSt opsac = MatchSt { minfo = []
                        , bvars = []
                        , opsac = opsac
                        }

instance Show MatchInfo where
    show mi = unwords ["Matching pat ="
                      , show $ patt mi
                      ,"con e ="
                      , show $ expr mi
                      ]
                
instance Show MatchSt where
    show mst = show (minfo mst)
