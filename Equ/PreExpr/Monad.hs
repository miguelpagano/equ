{-# Language TypeSynonymInstances, FlexibleInstances #-}
{-# Language MultiParamTypeClasses, FlexibleContexts #-}
module Equ.PreExpr.Monad 
    ( MonadTraversal
    , Log
    , localGo
    )
    where

import Equ.PreExpr.Zipper

import qualified Data.Text as T
import qualified Data.Sequence as S

import Data.Maybe (fromJust)
import Control.Monad.Trans.Class(lift)
import Control.Monad.Trans.Either(runEitherT, EitherT (..))
import Control.Monad.RWS (RWS)
import Control.Monad.RWS.Class ( local, tell, listen
                               , MonadState  (..)
                               , MonadReader (..)
                               , MonadWriter (..)
                               )

-- | Navegamos por el focus cambiando el enviroment.
localGo :: MonadReader Focus m => (Focus -> Maybe Focus) -> m a -> m a
localGo go = local (fromJust . go)

-- | Tipo correspondiente a nuestros logs.
type Log = S.Seq T.Text

{- | M&#243;nada de estado para preExpresiones (usando focus)
    La id&#233;a en esta monada es poder llevar, un log, un focus y un estado.
    El log lo tenemos para tener un poco de informaci&#243;n verbosa sobre que
    esta ocurriendo durante la computaci&#243;n.
    El focus lo utilizamos para tener contexto a cerca de donde estamos
    parados en relaci&#243;n a la expresi&#243;n, de la cual pretendemos comprobar alguna
    propiedad.
    El estado esta bastante libre, de momento la id&#233;a es utilizarlo para llevar
    las substituci&#243;nes resultantes de correr los algoritmos de matching y 
    type checking.
-}
type MonadTraversal e a = EitherT e (RWS Focus Log a)
    
-- | Instanc&#237;a de MonadWriter para utilizar el log.
instance MonadWriter Log (MonadTraversal e a) where
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

-- | Instanc&#237;a de MonadReader para navegar en el focus.
-- Vamos cambiando el ambiente conforme vamos haciendo recursi&#243;n en la
-- preExpresi&#243;n, es decir, navegando por el focus.
instance MonadReader Focus (MonadTraversal e a) where
    ask = lift ask
    local f m = EitherT $ local f (runEitherT m)

-- | Instanc&#237;a de MonadState
instance MonadState a (MonadTraversal e a) where
    get = lift get
    put s = lift (put s)
