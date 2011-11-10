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

import Graphics.UI.Gtk hiding (eventButton, eventSent, get)
import qualified Graphics.UI.Gtk as G

import Data.Text (unpack)

import Data.Reference
import Control.Arrow(first,second,(***),(&&&))
import Data.Maybe(fromJust)
import Control.Monad(liftM)
import Control.Monad.State(get,put,evalStateT)
import Control.Monad.Trans(liftIO)

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



{- Funciones que tienen que ver con el estado -} 
-- | Devuelve el estado.
askRef :: IState ProofState
askRef = get >>= readRef

-- | Devuelve el estado y la referencia.
askRef' :: IState (ProofState, ProofRef)
askRef' = get >>= \r -> readRef r >>= \s -> return (s,r)


-- | Consulta el estado y lo aplica a una computación con efectos.
withRefValue :: (ProofState -> IO a) -> IState a
withRefValue f = get >>= readRef >>= liftIO . f

-- | Consulta el estado, lo modifica de acuerdo al argumento y el
-- resultado de esta función pasa a ser el nuevo estado.
update :: (ProofState -> ProofState) -> IRProof
update f = get >>= \r -> readRef r >>= 
                        writeRef r . f >>
                        put r


-- | Realiza una acción en un estado modificado y luego vuelve al estado
-- anterior; devuelve el resultado de la acción.
local :: (ProofState -> IO a) -> IState a
local f = askRef >>= \s -> liftIO (f s) >>= \a -> update (const s) >> return a


-- | Realiza una acción en un estado modificado y luego vuelve al estado
-- anterior; devuelve el resultado de la acción.
local' :: (ProofState -> IState a) -> IState a
local' f = askRef >>= \oldState -> f oldState >>= \a -> 
           update (const oldState) >> return a

-- | Versión especializada de la anterior donde lo que se modifica es
-- el path.
localPath :: MGoBack -> IState a -> IState a
localPath p act = local' $ \st -> (updatePath . (p .^) . (path . focusedExpr)) st >> act


-- | Actualiza el mensaje que se muestra en el área de estado.
updateStatus :: String -> IState ()
updateStatus msg = withRefValue (\s -> putMsg (status s) msg) 

-- | Pone un mensaje en una área de estado.
putMsg :: StatusPlace -> String -> IO ()
putMsg st m = uncurry statusbarPush st m >> return ()

-- | Actualiza la expresión que se muestra en el área de estado;
-- esta es una función que puede dejar de tener sentido más adelante.
showExpr :: IState ()
showExpr = withRefValue $ uncurry putMsg . (status &&& show . toExpr . (expr . focusedExpr) )

{- Las tres funciones que siguen actualizan componentes particulares
del estado. -}
-- | Pone una nueva expresión en el lugar indicado por la función de ida-vuelta.
updateExpr e' = update updateExpr' >>
                showExpr                
                

updateExpr' :: ProofState -> ProofState
updateExpr' pst@(ProofState pr _ fexpr@(ExprFocus e (f,g) _) up _ _) = 
    pst {proof = modif pr new_expr,
         focusedExpr = fexpr {expr = new_expr
         }
    where new_expr = g . first (const e') . f $ e
    
{- Las tres funciones que siguen actualizan componentes particulares
del estado. -}
-- | Pone una nueva expresión en el lugar indicado por la función de ida-vuelta.
updateFocus :: Focus -> GoBack -> IState ()
updateFocus e' f = update (\pst -> pst {focusedExpr = (focusedExpr pst) {expr = e' , path = f}}) >>
                   showExpr

-- | Actualiza la caja donde tenemos foco de entrada.
updateFrmCtrl :: HBox -> IState ()
updateFrmCtrl l = update $ \pst -> pst { focusedExpr = (focusedExpr pst) {inpFocus = l }}

-- | Actualiza la lista de símbolos para construir expresiones.
updateSymCtrl :: TreeView -> IState ()
updateSymCtrl t = update $ \gst -> gst { symCtrl = t }

-- | Actualiza la función de ida-vuelta.
updatePath :: GoBack -> IState ()
updatePath p = update $ \pst -> pst { focusedExpr = (focusedExpr pst) {path = p }}

{- Las cinco funciones siguientes devuelven cada uno de los
componentes del estado. -}

getExpr :: IState Focus
getExpr = askRef >>= return . expr . focusedExpr

getFrmCtrl :: IState HBox
getFrmCtrl = askRef >>= return . inpFocus . focusedExpr

getSymCtrl :: IState TreeView
getSymCtrl = askRef >>= return . symCtrl

getAxiomCtrl :: IState TreeView
getAxiomCtrl = askRef >>= return . axiomCtrl

getPath :: IState GoBack
getPath  = askRef >>= return . path . focusedExpr

getStatus :: IState (Statusbar, ContextId)
getStatus  = askRef >>= return . status

{- Las dos funciones que siguen devuelven cada uno de los panes; toda la 
   gracia está en getParentNamed. -}

-- | Devuelve el paned que contiene la lista de símbolos.
getSymFrame :: IState Frame
getSymFrame = getSymCtrl >>= getParentNamed "symFrame". toWidget >>=
              return . castToFrame
              
getAxiomFrame :: IState Frame
getAxiomFrame = getAxiomCtrl >>= getParentNamed "axiomFrame" . toWidget >>=
                return . castToFrame

-- | Devuelve el paned que contiene al widget de fórmulas.
getFormPane :: IState Paned
getFormPane = getFrmCtrl >>=
              getParentNamed "formPane" . toWidget >>=
              return . castToPaned

-- | Devuelve el paned que contiene al widget de errores.
getFormErrPane :: IState Paned
getFormErrPane = getFrmCtrl >>= getParentNamed "errPane" . toWidget >>=
                 return . castToPaned

-- | Devuelve el label que reporta los errores.
getErrPanedLabel :: IState Label
getErrPanedLabel = getFormErrPane >>= \erp -> liftIO (panedGetChild1 erp) >>= 
                   \(Just l) -> return $ castToLabel l

-- | Devuelve el box de fórmulas.
getFormBox :: IState HBox
getFormBox = getFrmCtrl >>= getParentNamed "formulaBox" . toWidget >>=
             return . castToHBox

-- | Devuelve el ancestro que tiene un nombre. ¡Es insegura!
getParentNamed :: String -> Widget -> IState Widget
getParentNamed name = go
    where go w = liftIO (G.get w widgetName) >>= \name' ->
                 liftIO (putStrLn (maybe "Sin nombre" (\n -> if null n then "Nombre vacio" else n) name')) >>
                 if maybe False (== name) name'
                 then return w
                 else liftIO (widgetGetParent w) >>= go . fromJust


{- Listas heterógeneas de cosas que pueden agregarse a cajas -}
infixr 8 .*.

-- | Cons para listas heterogéneas.
(.*.) :: (WidgetClass w') => w' -> [Boxeable w] -> [Boxeable w]
w .*. ws = Boxeable w : ws

infix 9 .*:
-- | @ a .*: b == [a,b]@ para listas heterogéneas.
(.*:) :: (WidgetClass w',WidgetClass w) => w' -> w -> [Boxeable w]
w' .*: w = Boxeable w' : Boxeable w : []


-- TODO: Manejo de errores; por ejemplo mostrando un dialog con 
-- el error.
-- | Las dos funciones que siguen parsean variables y luego aplican
-- funciones si el resultado es exitoso.
parseVar :: (Variable -> IState ()) -> String -> IState ()
parseVar f = either (return $ return ()) f . parserVar

-- | Especialización para cuando queremos ver la variable como una
-- expresión.
parseVarE :: (PreExpr -> IState ()) -> String -> IState ()
parseVarE f = parseVar (f . Var)


-- TODO: debemos hacer renombre si la variable está ligada?
-- | Actualización de la variable de cuantificación.
updateQVar :: String -> IState ()
updateQVar v = getExpr >>= \e ->                
               case fst e of
                 Quant q _ r t -> parseVar (\v' -> updateExpr (Quant q v' r t)) v
                 _ -> return ()



-- | Ejecuta una acción en la mónada de estado para obtener un
-- resultado. Es útil para los event-handlers.
withState :: (IO a -> IO b) -> IState a -> IState b
withState f m = get >>= liftIO . f . evalStateT m

eventWithState :: IState a -> ProofRef -> EventM t a
eventWithState m = liftIO . evalStateT m
