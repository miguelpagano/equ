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
import Equ.Proof(ProofFocus,updateStartFocus,updateEndFocus)
import Equ.Rule

import Equ.Types

import Graphics.UI.Gtk hiding (eventButton, eventSent, get)

import qualified Graphics.UI.Gtk as G

import Data.Text (unpack)
import Data.List

import Data.Reference
import Control.Arrow(first,second,(***),(&&&))
import Data.Maybe(fromJust)
import Control.Monad(liftM)
import Control.Monad.State(get,put,evalStateT)
import Control.Monad.Trans(liftIO)

import qualified Data.Serialize as S
import qualified Data.ByteString as L

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
update :: (GState -> GState) -> IRG
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
localPath p act = local' $ \st -> (updatePath . (p .^) . (pathExpr . fromJust . gExpr)) st >> act

-- | Actualiza el mensaje que se muestra en el área de estado.
updateStatus :: String -> IState ()
updateStatus msg = withRefValue (\s -> putMsg (status s) msg) 

-- | Pone un mensaje en una área de estado.
putMsg :: StatusPlace -> String -> IO ()
putMsg st m = uncurry statusbarPush st m >> return ()

-- | Actualiza la expresión que se muestra en el área de estado;
-- esta es una función que puede dejar de tener sentido más adelante.
showExpr :: IState ()
showExpr = withRefValue $ uncurry putMsg . (status &&& show . toExpr . (fExpr . fromJust . gExpr) )

showProof :: IState ()
showProof = withRefValue $ uncurry putMsg . (status &&& show . proof . fromJust . gProof )

{- Las tres funciones que siguen actualizan componentes particulares
del estado. -}
-- | Pone una nueva expresión en el lugar indicado por la función de ida-vuelta.
updateExpr e' = update (updateExpr' e') >> showExpr

updateExpr' :: PreExpr -> GState -> GState
updateExpr' _ gst@(GState Nothing _ _ _ _ _ _ _ _ _ _) = gst
updateExpr' _ gst@(GState _ Nothing _ _ _ _ _ _ _ _ _) = gst
updateExpr' e' gst@(GState (Just gpr) (Just gexpr)_ _ _ _ _ _ _ _ _) = 
    gst { gProof = Just $ gpr {proof = fromJust $ up pr newExpr}
        , gExpr = Just $ gexpr {fExpr = newExpr}
        }
    where
        newExpr :: Focus
        newExpr = g . first (const e') . f $ e
        pr :: ProofFocus
        pr = proof gpr
        up :: ProofFocus -> Focus -> Maybe ProofFocus
        up = modifExpr gpr
        e :: Focus
        e = fExpr gexpr
        f,g :: Move
        (f,g) = pathExpr gexpr
    
updateProof pf = update (updateProof' pf) >>
                showProof >>
                getProof >>= \p -> liftIO (putStrLn (show p))

updateProof' :: ProofFocus -> GState -> GState
updateProof' _ gst@(GState Nothing _ _ _ _ _ _ _ _ _ _) = gst
updateProof' _ gst@(GState _ Nothing _ _ _ _ _ _ _ _ _) = gst
updateProof' (p,path) gst@(GState (Just gpr) (Just gexpr) _ _ _ _ _ _ _ _ _) = 
    gst { gProof = Just $ gpr { proof = (p,path)
                              , modifExpr = updateStartFocus
                              }
        , gExpr = Just $ gexpr { fExpr = fromJust $ getStart p
                               , pathExpr = (id,id)
                             }
        }
    where
        pr :: ProofFocus
        pr = proof gpr
        up :: ProofFocus -> Focus -> Maybe ProofFocus
        up = modifExpr gpr
        e :: Focus
        e = fExpr gexpr
        f,g :: Move
        f = fst $ pathExpr gexpr
        g = snd $ pathExpr gexpr

updateProofState :: ProofState -> IState ()
updateProofState ps = update (\gst -> gst {gProof = Just ps})

updateExprState :: ExprState -> IState ()
updateExprState es = update (\gst -> gst {gExpr = Just es})

updateSelectedExpr :: (ProofFocus -> Focus) -> IState ()
updateSelectedExpr f = do
    maybe_es <- getSelectExpr
    case maybe_es of
         Nothing -> return ()
         (Just es) -> do
            pf <- getProof
            updateExprState (es {fExpr= f pf})

{- Las tres funciones que siguen actualizan componentes particulares
del estado. -}
-- | Pone una nueva expresión en el lugar indicado por la función de ida-vuelta.
updateFocus :: Focus -> GoBack -> IState ()
updateFocus e' f = update (updateFocus' e' f) >> 
                   liftIO (putStrLn "updateFocus") >> 
                   showProof

updateFocus' :: Focus -> GoBack -> GState -> GState
updateFocus' _ _ gst@(GState _ Nothing _ _ _ _ _ _ _ _ _) = gst
updateFocus' (e,p) (f,g) gst@(GState _ (Just gexpr) _ _ _ _ _ _ _ _ _) = 
                                    gst { gExpr = Just $ gexpr { fExpr = (e,p)
                                                               , pathExpr = (f,g)
                                                               }
                                        }

-- | Actualiza la caja donde tenemos foco de entrada.
updateFrmCtrl :: HBox -> IState ()
updateFrmCtrl l = update (\gst -> case gExpr gst of
                                        Nothing -> gst
                                        Just es -> gst { gExpr = Just $ es {eventExpr = l }})

-- | Actualiza la lista de símbolos para construir expresiones.
updateSymCtrl :: TreeView -> IState ()
updateSymCtrl t = update $ \gst -> gst { symCtrl = t }

-- | Actualiza la función de ida-vuelta.
updatePath :: GoBack -> IState ()
updatePath p = update $ \gst -> gst { gExpr = Just $ ((fromJust . gExpr) gst) { pathExpr = p}}

updateModifExpr :: (ProofFocus -> Focus -> Maybe ProofFocus) -> IState ()
updateModifExpr f = update $ \gst -> gst { gProof = Just $ ((fromJust . gProof) gst) {modifExpr = f}}

updateRelation :: Relation -> IState ()
updateRelation r = getProof >>= \(p,path) ->
                   updateProof (updateRel p r,path)
                   
updateAxiomBox :: HBox -> IState ()
updateAxiomBox b = update $ \gst -> gst {gProof = Just $ ((fromJust . gProof) gst) {axiomBox = b}}

changeProofFocus :: (ProofFocus -> Maybe ProofFocus) -> HBox -> IState ()
changeProofFocus moveFocus box = getProof >>= \pf -> updateProof (fromJust $ moveFocus pf) >>
                                 updateAxiomBox box

{- Las nueve funciones siguientes devuelven cada uno de los
componentes del estado. -}

getProof :: IState ProofFocus
getProof = (liftIO $ putStrLn "getProof") >> askRef >>= return . proof . fromJust . gProof

getProofState :: IState (Maybe ProofState)
getProofState = (liftIO $ putStrLn "getProofState") >> askRef >>= return . gProof

getExpr :: IState Focus
getExpr = (liftIO $ putStrLn "getExpr") >> askRef >>= return . fExpr . fromJust . gExpr

getFrmCtrl :: IState HBox
getFrmCtrl = (liftIO $ putStrLn "getFrmCtrl") >> askRef >>= return . eventExpr . fromJust . gExpr

getSelectExpr :: IState (Maybe ExprState)
getSelectExpr = (liftIO $ putStrLn "getSelectExpr") >> askRef >>= return . gExpr

getTreeExpr :: IState TreeExpr
getTreeExpr = askRef >>= return . gTreeExpr

getFaces :: IState Notebook
getFaces = askRef >>= return . gFaces

getSymCtrl :: IState TreeView
getSymCtrl = (liftIO $ putStrLn "getSymCtrl") >> askRef >>= return . symCtrl

getAxiomCtrl :: IState TreeView
getAxiomCtrl = (liftIO $ putStrLn "getAxiomCtrl") >> askRef >>= return . axiomCtrl

getPath :: IState GoBack
getPath  = (liftIO $ putStrLn "getPath") >> askRef >>= return . pathExpr . fromJust . gExpr

getStatus :: IState (Statusbar, ContextId)
getStatus  = (liftIO $ putStrLn "getStatus") >> askRef >>= return . status

getAxiomBox :: IState HBox
getAxiomBox = (liftIO $ putStrLn "getAxiomBox") >> askRef >>= return . axiomBox . fromJust . gProof

{- Las dos funciones que siguen devuelven cada uno de los panes; toda la 
   gracia está en getParentNamed. -}

getTreeExprBox :: IState VBox
getTreeExprBox = getFaces >>= \f -> liftIO (notebookGetNthPage f 1) >>= 
                 \(Just w) -> liftIO (containerGetChildren (castToBox w)) >>= 
                 \[_,w] -> liftIO (containerGetChildren (castToBox w)) >>= 
                 \[_,m] -> return $ castToVBox m

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
-- TODO: Queda muy fea la parte de la lista con tres elementos.
getErrPane :: IState Paned
getErrPane = getStatus >>= liftIO . widgetGetParent . fst >>= \(Just w) ->
             liftIO (containerGetChildren (castToContainer w)) >>= \[_,m,_] ->
             return $ castToPaned m

-- | Devuelve el label que reporta los errores.
getErrPanedLabel :: IState EventBox
getErrPanedLabel = getErrPane >>= \erp -> liftIO (panedGetChild1 erp) >>= 
                   \(Just eb) -> return $ castToEventBox eb

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

selectExprFromBox :: HBox -> IState ()
selectExprFromBox = selectFrom (eventExpr)

selectTypeFromBox :: HBox -> IState ()
selectTypeFromBox = selectFrom (eventType)

selectFrom :: (ExprState -> HBox) -> HBox -> IState ()
selectFrom eventTE eb = getTreeExpr >>= \tl ->
                   case find (\te -> (eventTE te) == eb) tl of
                        Nothing -> return ()
                        Just se -> update (\gst -> gst {gExpr = Just se})

updateExprSelectExpr :: ExprState -> PreExpr -> IState ()
updateExprSelectExpr es e = update (\gst -> gst {gExpr = Just es'})
    where
        es' :: ExprState
        es' = es {fExpr = (toFocus . toExpr . (flip replace $ e) . fExpr) es}

updateTypeSelectType :: ExprState -> Type -> IState ()
updateTypeSelectType es t = update (\gst -> gst {gExpr = Just es'})
    where
        es' :: ExprState
        es' = es {fType = t}

updateTypedTypeFromTree :: ExprState -> Type -> IState ()
updateTypedTypeFromTree te t = getTreeExpr >>= \fl ->
                    case find (\te' -> (eventExpr te') == (eventExpr te)) fl of
                        Nothing -> return ()
                        Just se -> return (deleteBy 
                                            (\se -> \se' -> 
                                            eventExpr se == eventExpr se') 
                                            se fl) >>= \fl' ->
                                    update (\gst -> gst {gTreeExpr = (se {fType = t}) : fl'})

cleanTreeExpr :: IState ()
cleanTreeExpr = update (\gst -> gst { gTreeExpr = []})

-- Añade una expresion y su respectivo boton a al arbol de tipado.
addExprToTree :: Focus -> Type -> GoBack -> HBox -> HBox -> IState ExprState
addExprToTree f t p be bt = update (\gst@(GState _ _ gte _ _ _ _ _ _ _ _) -> 
                                    gst { gTreeExpr = te : gte}) >> return te
    where te :: ExprState
          te = ExprState { fExpr = f
                         , fType = t
                         , pathExpr = p
                         , eventExpr = be
                         , eventType = bt
                         }

-- | Ejecuta una acción en la mónada de estado para obtener un
-- resultado. Es útil para los event-handlers.
withState :: (IO a -> IO b) -> IState a -> IState b
withState f m = get >>= liftIO . f . evalStateT m

eventWithState :: IState a -> GRef -> EventM t a
eventWithState m = liftIO . evalStateT m


-- DONDE VAN ESTAS FUNCIONES???
encodeFile :: S.Serialize a => FilePath -> a -> IO ()
encodeFile f v = L.writeFile f (S.encode v)
 
decodeFile :: S.Serialize a => FilePath -> IO a
decodeFile f = do s <- L.readFile f
                  either (error) (return) $ S.runGet (do v <- S.get
                                                         m <- S.isEmpty
                                                         m `seq` return v) s
                                                         
setFileFilter :: FileChooserClass f => f -> String -> String -> IO ()
setFileFilter fChooser pattern title = do
    hsfilt <- fileFilterNew
    fileFilterAddPattern hsfilt pattern
    fileFilterSetName hsfilt title
    fileChooserAddFilter fChooser hsfilt
                                            

