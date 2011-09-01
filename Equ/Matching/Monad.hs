{-# Language TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}
-- | Definición de la mónada de matching y sus instancias.
module Equ.Matching.Monad where

import Equ.PreExpr
import Equ.Matching.Error

import qualified Data.Map as M
import qualified Data.Text as T
import qualified Data.Sequence as S

-- import Control.Arrow
import Control.Monad.Trans.Class
import Control.Monad.Trans.Either
import Control.Monad.RWS (RWS)
import Control.Monad.RWS.Class

type ExprSubst = M.Map Variable PreExpr

-- | Tipo correspondiente a nuestros logs.
type Log = S.Seq T.Text

-- | El error está acompañado de la expresión enfocada donde ocurrió.
type MatchMErr = (Focus,MatchError)

-- TODO: cambiar: el estado tendría el contexto además de la
-- sustitución.
-- | La mónada de estado del type-checker.
type MatchState = EitherT MatchMErr (RWS Focus Log ExprSubst) 

instance MonadWriter Log MatchState where
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

instance MonadReader Focus MatchState where
    ask = lift ask
    local f m = EitherT $ local f (runEitherT m)

instance MonadState ExprSubst MatchState where
    get = lift get
    put s = lift (put s)

-- | Agrega una línea de log.
addLog :: String -> MatchState ()
addLog s = tell . S.fromList $ [T.pack s]

-- | Generación de mensaje de Error.
matcherr :: MatchError -> MatchState a
matcherr err = ask >>= \foc -> hoistEither $ Left (foc, err)
