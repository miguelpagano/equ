{-# Language OverloadedStrings #-}
-- | Utilidades varias que tienen que ver con el estado de la
-- interfaz (es probable que se muden a Equ.GUI.State) y con
-- funciones convenientes que podrían mudarse a otros módulos.
module Equ.GUI.State.Internal 
    ( askRef
    , askRef'
    , withRefValue
    , update
    , local
    , local'
    , getStatePart
    , getStatePartDbg
    , updateStatus
    , module Control.Monad.State.Strict
    )
where

import Equ.GUI.Types
import Equ.GUI.Utils

import Data.Reference
import Control.Monad(liftM,when)
import Control.Monad.State.Strict (get,put,evalStateT)


{- Funciones que tienen que ver con el estado -} 
-- | Devuelve el estado.
askRef :: IState GState
askRef = get >>= readRef

-- | Devuelve el estado y la referencia.
askRef' :: IState (GState, GRef)
askRef' = get >>= \r -> readRef r >>= \s -> return (s,r)

-- | Consulta el estado y lo aplica a una computación con efectos.
withRefValue :: (GState -> IO a) -> IState a
withRefValue f = get >>= readRef >>= io . f

-- | Consulta el estado, lo modifica de acuerdo al argumento y el
-- resultado de esta función pasa a ser el nuevo estado.
update :: (GState -> GState) -> IRG
update f = get >>= \r -> readRef r >>= 
                        writeRef r . f >>
                        put r

-- | Realiza una acción en un estado modificado y luego vuelve al estado
-- anterior; devuelve el resultado de la acción.
local :: (GState -> IO a) -> IState a
local f = askRef >>= \s -> io (f s) >>= \a -> update (const s) >> return a

-- | Realiza una acción en un estado modificado y luego vuelve al estado
-- anterior; devuelve el resultado de la acción.
local' :: (GState -> IState a) -> IState a
local' f = askRef >>= \oldState -> f oldState >>= \a -> 
           update (const oldState) >> return a

-- | Devuelve un componente del estado.
getStatePart :: (GState -> a) -> IState a
getStatePart part = askRef >>= return . part

-- | Devuelve un componente del estado e imprime un mensaje en
-- la consola. NO USAR EN LO POSIBLE.
getStatePartDbg :: String -> (GState -> a) -> IState a
getStatePartDbg msg part = (io $ debug msg) >> getStatePart part

-- | Actualiza el mensaje que se muestra en el área de estado.
updateStatus :: String -> IState ()
updateStatus msg = withRefValue (\s -> putMsg (status s) msg) 
