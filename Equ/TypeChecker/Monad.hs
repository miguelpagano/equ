{-# Language TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}
module Equ.TypeChecker.Monad where


import Equ.PreExpr
import Equ.Types
import Equ.TypeChecker.Error

import qualified Data.Map as M
import qualified Data.Sequence as S
import Data.Maybe (fromJust)

-- import Control.Arrow
import Control.Monad.Trans.Class
import Control.Applicative
import Control.Monad.Trans.Either
import Control.Monad.RWS (RWS,rws)
import Control.Monad.RWS.Class



-- | Tipo de la sustitución para unificar expresiones de tipo.
type TySubst = M.Map TyVarName Type

-- TODO: cambiar la mónada de chequeo de tipos; debería ser un mónada
-- de error dentro de una mónada de estado: el estado tendría el foco
-- y el contexto.

type Log = S.Seq String
type TMErr = (Focus,TyErr)

type TyState = EitherT TMErr (RWS Focus Log TySubst) 

instance MonadWriter Log TyState where
    tell w = lift (tell w)
    listen m = EitherT $ do 
                 (a,w) <- listen (runEitherT m)
                 case a of
                   Left f -> return $ Left f
                   Right r -> return $ Right (r,w)
    pass m = EitherT $ pass $ do
               a <- runEitherT m
               case a of
                 Left f -> return $ (Left f,id)
                 Right (r,f) -> return $ (Right r,f)

instance MonadReader Focus TyState where
    ask = lift ask
    local f m = EitherT $ local f (runEitherT m)

instance MonadState TySubst TyState where
    get = lift get
    put s = lift (put s)

-- | Agrega una línea de log.
addLog :: String -> TyState ()
addLog s = tell . S.fromList $ [s]

-- | Generación de mensaje de Error.
tyerr :: TyErr -> TyState a
tyerr err = ask >>= \foc -> hoistEither $ Left (foc, err)
