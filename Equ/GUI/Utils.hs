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

{- Las dos funciones siguientes podrían ir a Equ.PreExpr... -}
-- | Un hueco sin información.
holeExpr :: PreExpr
holeExpr = preExprHole ""

emptyExpr :: Focus
emptyExpr = toFocus holeExpr

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
askRef :: IState GState
askRef = get >>= readRef

-- | Devuelve el estado y la referencia.
askRef' :: IState (GState, GRef)
askRef' = get >>= \r -> readRef r >>= \s -> return (s,r)


-- | Consulta el estado y lo aplica a una computación con efectos.
withRefValue :: (GState -> IO a) -> IState a
withRefValue f = get >>= readRef >>= liftIO . f

-- | Consulta el estado, lo modifica de acuerdo al argumento y el
-- resultado de esta función pasa a ser el nuevo estado.
update :: (GState -> GState) -> IRExpr
update f = get >>= \r -> readRef r >>= 
                        writeRef r . f >>
                        put r

-- | Realiza una acción en un estado modificado y luego vuelve al estado
-- anterior; devuelve el resultado de la acción.
local :: (GState -> IO a) -> IState a
local f = askRef >>= \s -> liftIO (f s) >>= \a -> update (const s) >> return a


-- | Realiza una acción en un estado modificado y luego vuelve al estado
-- anterior; devuelve el resultado de la acción.
local' :: (GState -> IState a) -> IState a
local' f = askRef >>= \oldState -> f oldState >>= \a -> 
           update (const oldState) >> return a

-- | Versión especializada de la anterior donde lo que se modifica es
-- el path.
localPath :: MGoBack -> IState a -> IState a
localPath p act = local' $ \st -> (updatePath . (p .^) . path) st >> act


-- | Actualiza el mensaje que se muestra en el área de estado.
updateStatus :: String -> IState ()
updateStatus msg = withRefValue (\s -> putMsg (status s) msg) 

-- | Pone un mensaje en una área de estado.
putMsg :: StatusPlace -> String -> IO ()
putMsg st m = uncurry statusbarPush st m >> return ()

-- | Actualiza la expresión que se muestra en el área de estado;
-- esta es una función que puede dejar de tener sentido más adelante.
showExpr :: IState ()
showExpr = withRefValue $ uncurry putMsg . (status &&& show . toExpr . expr)

{- Las tres funciones que siguen actualizan componentes particulares
del estado. -}
-- | Pone una nueva expresión en el lugar indicado por la función de ida-vuelta.
updateExpr :: PreExpr -> IState ()
updateExpr e' = update (\gst@(GState e _ _ _ _ (f,g) _) -> 
                        gst {expr = g . first (const e') . f $ e }) >>
                showExpr

{- Las tres funciones que siguen actualizan componentes particulares
del estado. -}
-- | Pone una nueva expresión en el lugar indicado por la función de ida-vuelta.
updateFocus :: Focus -> GoBack -> IState ()
updateFocus e' f = update (\gst -> gst {expr = e' , path = f}) >>
                   showExpr

-- | Actualiza la caja donde tenemos foco de entrada.
updateFrmCtrl :: HBox -> IState ()
updateFrmCtrl l = update $ \gst -> gst { inpFocus = l }

-- | Actualiza la lista de símbolos para construir expresiones.
updateSymCtrl :: TreeView -> IState ()
updateSymCtrl t = update $ \gst -> gst { symCtrl = t }

-- | Actualiza la función de ida-vuelta.
updatePath :: GoBack -> IState ()
updatePath p = update $ \gst -> gst { path = p }

{- Las nueve funciones siguientes devuelven cada uno de los
componentes del estado. -}

getExpr :: IState Focus
getExpr = askRef >>= return . expr

getFrmCtrl :: IState HBox
getFrmCtrl = askRef >>= return . inpFocus

getTypedOptionPane :: IState HPaned
getTypedOptionPane = askRef >>= return . typedOptionPane

getTypedFormPane :: IState VPaned
getTypedFormPane = askRef >>= return . paned . typedFormPane

getTypedFormList :: IState TBExprList
getTypedFormList = askRef >>= return . formList . typedFormPane

getTypedFormTree :: IState TBExprList
getTypedFormTree = askRef >>= return . formTree . typedFormPane

getSymCtrl :: IState TreeView
getSymCtrl = askRef >>= return . symCtrl

getPath :: IState GoBack
getPath  = askRef >>= return . path

getStatus :: IState (Statusbar, ContextId)
getStatus  = askRef >>= return . status

{- Las dos funciones que siguen devuelven cada uno de los panes; toda la 
   gracia está en getParentNamed. -}

-- | Devuelve el paned que contiene la lista de símbolos.
getSymPane :: IState Paned
getSymPane = getSymCtrl >>= getParentNamed "symPane". toWidget >>=
              return . castToPaned

-- | Devuelve el paned que contiene al widget de fórmulas.
getFormPane :: IState Paned
getFormPane = getFrmCtrl >>= getParentNamed "formPane" . toWidget >>=
              return . castToPaned

-- | Devuelve el paned que contiene al widget de errores.
getFormErrPane :: IState Paned
getFormErrPane = getFrmCtrl >>= getParentNamed "errPane" . toWidget >>=
                return . castToPaned

-- | Devuelve el label que reporta los errores.
getErrPanedLabel :: IState Label
getErrPanedLabel = getFormErrPane >>= \erp -> liftIO (panedGetChild1 erp) >>= 
                   \(Just l) -> return $ castToLabel l

getFormBox :: IState HBox
getFormBox = getFrmCtrl >>= getParentNamed "formulaBox" . toWidget >>=
             return . castToHBox

-- | Retorna el box que contiene a las expresiones tipadas.
getTypedFormBox :: IState VBox
getTypedFormBox = getTypedFormPane >>= \p -> liftIO (panedGetChild1 p) >>= 
                  \(Just c) -> (return . castToVBox) c

-- | Retorna el box que contiene a las expresiones que constituyen el arbol
--  de tipado de una expresión.
getBoxTypedFormTree :: IState VBox
getBoxTypedFormTree = getTypedFormPane >>= \p -> liftIO (panedGetChild2 p) >>= 
                     \(Just c) -> (return . castToVBox) c

-- | Devuelve el ancestro que tiene un nombre. ¡Es insegura!
getParentNamed :: String -> Widget -> IState Widget
getParentNamed name = go
    where go w = liftIO (G.get w widgetName) >>= \name' ->
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

-- Añade una expresion y su respectivo boton a la lista de expresiones.
addToggleButtonList :: PreExpr -> ToggleButton -> IState ()
addToggleButtonList e tb = update $ \gst@(GState _ _ _ tp _ _ _) -> 
                            gst {typedFormPane = 
                                    tp {formList =  WExpr { widget = tb
                                                            , wexpr = e
                                                            } : (formList tp)}
                                      }

-- Añade una expresion y su respectivo boton a al arbol de tipado.
addToggleButtonTree :: PreExpr -> ToggleButton -> IState ()
addToggleButtonTree e tb = update $ \gst@(GState _ _ _ tp _ _ _) -> 
                            gst {typedFormPane = 
                                    tp {formTree =  WExpr { widget = tb
                                                            , wexpr = e
                                                            } : (formTree tp)}
                                      }

-- | Ejecuta una acción en la mónada de estado para obtener un
-- resultado. Es útil para los event-handlers.
withState :: (IO a -> IO b) -> IState a -> IState b
withState f m = get >>= liftIO . f . evalStateT m

eventWithState :: IState a -> GRef -> EventM t a
eventWithState m = liftIO . evalStateT m
