{-# Language TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}
-- | Definición de la mónada del type-checker y sus instancias.
module Equ.TypeChecker.Monad where


import Equ.PreExpr
import Equ.Types
import Equ.TypeChecker.Error

import qualified Data.Map as M
import qualified Data.Text as T
import qualified Data.Sequence as S

-- import Control.Arrow
import Control.Monad.Trans.Class
import Control.Monad.Trans.Either
import Control.Monad.RWS (RWS)
import Control.Monad.RWS.Class


-- | Tipo de la sustitución para unificar expresiones de tipo.
type TySubst = M.Map TyVarName Type

-- | Tipo correspondiente a nuestros logs.
type Log = S.Seq T.Text

-- | El error está acompañado de la expresión enfocada donde ocurrió.
type TMErr = (Focus,TyErr)

-- TODO: cambiar: el estado tendría el contexto además de la
-- sustitución.
-- | La mónada de estado del type-checker.
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
addLog s = tell . S.fromList $ [T.pack s]

-- | Generación de mensaje de Error.
tyerr :: TyErr -> TyState a
tyerr err = ask >>= \foc -> hoistEither $ Left (foc, err)
