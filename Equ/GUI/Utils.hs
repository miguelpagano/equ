{-# Language OverloadedStrings #-}
-- | Utilidades varias que tienen que ver con el estado de la
-- interfaz (es probable que se muden a Equ.GUI.State) y con
-- funciones convenientes que podrían mudarse a otros módulos.
module Equ.GUI.Utils where

import Equ.GUI.Types

import Equ.Expr
import Equ.PreExpr
import Equ.Theories
import Equ.Syntax
import Equ.Parser

import Equ.Proof.Proof
import Equ.Proof.Error(errEmptyProof)
import Equ.Proof(ProofFocus,updateStartFocus,updateEndFocus,PM,validateProof,toProof)
import Equ.Rule

import Equ.Types

import Graphics.UI.Gtk hiding (eventButton, eventSent, get)

import qualified Graphics.UI.Gtk as G
import System.Glib.GType
import System.Glib.GObject

import Data.Text (unpack)
import Data.List
import Data.Either(rights)

import Data.Reference
import Control.Arrow(first,second,(***),(&&&))
import Data.Maybe(fromJust)
import Control.Monad(liftM)
import Control.Monad.State(get,put,evalStateT)
import Control.Monad.Trans(liftIO)


import qualified Data.Serialize as S
import qualified Data.ByteString as L
import qualified Data.Foldable as F (mapM_) 

-- | 
withJust :: Monad m => Maybe a -> (a -> m ()) -> m ()
withJust = flip F.mapM_

-- | Composición bastante usada; podría ir a Equ.PreExpr.Internal.
repr :: Syntactic t => t -> String
repr = unpack . tRepr

{- Las tres funciones que siguen podrían ir a Equ.PreExpr.Zipper -}
-- | Una función insegura; sólo la usamos cuando sabemos que la usamos
-- bien.
go :: (Focus -> Maybe Focus) -> Move
go g e = maybe (error $ show e) id $ g e

-- | Composición de ida-vuelta.
(.^.) :: GoBack -> GoBack -> GoBack
(f,f') .^. (g,g') = (f . g , g' . f')

-- | Composición (insegura) de ida-vueltas.
(.^) :: (Focus -> Maybe Focus,Focus -> Maybe Focus) -> GoBack -> GoBack
(f,f') .^ (g,g') = (go f . g , g' . go f')


-- | Pone un mensaje en una área de estado.
putMsg :: StatusPlace -> String -> IO ()
putMsg st m = uncurry statusbarPush st m >> return ()
                 
{- Listas heterógeneas de cosas que pueden agregarse a cajas -}
-- TODO: Estamos usando estas funciones?
infixr 8 .*.

-- | Cons para listas heterogéneas.
(.*.) :: (WidgetClass w') => w' -> [Boxeable w] -> [Boxeable w]
w .*. ws = Boxeable w : ws

infix 9 .*:
-- | @ a .*: b == [a,b]@ para listas heterogéneas.
(.*:) :: (WidgetClass w',WidgetClass w) => w' -> w -> [Boxeable w]
w' .*: w = Boxeable w' : Boxeable w : []

-- DONDE VAN ESTAS FUNCIONES???
encodeFile :: S.Serialize a => FilePath -> a -> IO ()
encodeFile f v = L.writeFile f (S.encode v)
 
decodeFile :: S.Serialize a => FilePath -> IO a
decodeFile f = L.readFile f >>= 
               either error return .
                      S.runGet (S.get >>= \v ->
                                S.isEmpty >>= \m ->
                                m `seq` return v)
                                                         
setFileFilter :: FileChooserClass f => f -> String -> String -> IO ()
setFileFilter fChooser pattern title = do
    hsfilt <- fileFilterNew
    fileFilterAddPattern hsfilt pattern
    fileFilterSetName hsfilt title
    fileChooserAddFilter fChooser hsfilt



isVBox :: WidgetClass w => w -> Bool
isVBox w = isA w gTypeVBox 

isHBox :: WidgetClass w => w -> Bool
isHBox w = isA w gTypeHBox 

fromRight = head . rights . return          

-- | Funcion para emitir mensajes de debugging.
debug :: String -> IO ()
debug = putStrLn
--debug = const $ return ()