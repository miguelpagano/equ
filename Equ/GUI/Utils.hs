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
import Equ.Proof(ProofFocus,updateStartFocus,updateEndFocus,PM,validateProof,toProof)
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
updateExpr' e' gst = case (gProof gst,gExpr gst) of
                      (Just gpr, Just gexpr) -> upd gpr gexpr 
                      (_,_) -> gst
    where upd gpr gexpr = gst { gProof = Just gpr' 
                              , gExpr = Just gexpr' 
                              }
              where  gpr' = gpr {proof = fromJust $ up (proof gpr) newExpr}
                     up = modifExpr gpr
                     gexpr' = gexpr {fExpr = newExpr}
                     newExpr = g . first (const e') $ f e
                     e = fExpr gexpr
                     (f,g) = pathExpr gexpr
    
updateProof pf = update (updateProof' pf) >>
                showProof >>
                getProof >>= liftIO . putStrLn . show

updateProof' :: ProofFocus -> GState -> GState
updateProof' (p,path) gst = case (gProof gst,gExpr gst) of
                              (Just gpr,Just gexpr) -> upd gpr gexpr
                              (_,_) -> gst
    where upd gpr gexpr = gst { gProof = Just gpr { proof = (p,path)
                                                  , modifExpr = updateStartFocus
                                                  }
                              , gExpr = Just $ gexpr { fExpr = fromJust $ getStart p
                                                     , pathExpr = (id,id)
                                                     }
                              }
              where pr = proof gpr
                    up = modifExpr gpr
                    e = fExpr gexpr
                    (f,g) = pathExpr gexpr
        
-- | Valida la prueba y actualiza el campo "validProof" del ProofState
updateValidProof :: IState ()
updateValidProof = getValidProof >>= \vp -> update (updateValidProof' vp)
    where updateValidProof' :: PM Proof -> GState -> GState
          updateValidProof' vp gst = case gProof gst of
                                       Just gpr -> gst { gProof = Just $ updPrf gpr }
                                       Nothing -> gst
          updPrf gpr = gpr { validProof = validateProof (toProof $ proof gpr) }

updateProofState :: ProofState -> IState ()
updateProofState ps = update (\gst -> gst {gProof = Just ps})

updateExprState :: ExprState -> IState ()
updateExprState es = update (\gst -> gst {gExpr = Just es})

updateSelectedExpr :: (ProofFocus -> Focus) -> IState ()
updateSelectedExpr f = getSelectExpr >>= F.mapM_ 
                       (\es -> getProof >>= \ pf -> 
                              updateExprState (es {fExpr= f pf}))

{- Las tres funciones que siguen actualizan componentes particulares
del estado. -}
-- | Pone una nueva expresión en el lugar indicado por la función de ida-vuelta.
updateFocus :: Focus -> GoBack -> IState ()
updateFocus e' f = update (updateFocus' e' f) >> 
                   liftIO (putStrLn "updateFocus") >> 
                   showProof

updateFocus' :: Focus -> GoBack -> GState -> GState
updateFocus' (e,p) (f,g) gst = case gExpr gst of
                                 Just gexpr -> gst { gExpr = Just $ upd gexpr }
                                 Nothing -> gst
    where upd gexpr = gexpr { fExpr = (e,p)
                            , pathExpr = (f,g)
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

addTheorem :: Theorem -> IState Theorem
addTheorem th = (update $ \gst -> gst { theorems = (th:theorems gst) }) >>
                return th

changeProofFocus :: (ProofFocus -> Maybe ProofFocus) -> HBox -> IState ()
changeProofFocus moveFocus box = getProof >>= \pf -> updateProof (fromJust $ moveFocus pf) >>
                                 updateAxiomBox box
                              

{- Las nueve funciones siguientes devuelven cada uno de los
componentes del estado. -}

getStatePart :: (GState -> a) -> IState a
getStatePart part = askRef >>= return . part


getStatePartDbg :: String -> (GState -> a) -> IState a
getStatePartDbg msg part = (liftIO $ putStrLn msg) >> getStatePart part

getProof :: IState ProofFocus
getProof = getStatePartDbg "getProof" (proof . fromJust . gProof)

getValidProof :: IState (PM Proof)
getValidProof = getStatePart $ validProof . fromJust . gProof

getProofState :: IState (Maybe ProofState)
getProofState = getStatePartDbg "getProofState" gProof

getExprProof :: IState Expr
getExprProof = getValidProof >>= either (const (return holeExpr)) (return . getExpr)                    
    where getExpr p = Expr $ BinOp (relationToOperator (fromJust $ getRel p))
                                   (toExpr $ fromJust $ getStart p)
                                   (toExpr $ fromJust $ getEnd p)
                                     

getExpr :: IState Focus
getExpr = getStatePartDbg "getExpr" $ fExpr . fromJust . gExpr

getFrmCtrl :: IState HBox
getFrmCtrl = getStatePartDbg "getFrmCtrl" $ eventExpr . fromJust . gExpr

getSelectExpr :: IState (Maybe ExprState)
getSelectExpr = getStatePartDbg "getSelectExpr" gExpr

getTreeExpr :: IState (Maybe TreeExpr)
getTreeExpr = getStatePart gTreeExpr

getFaces :: IState Notebook
getFaces = getStatePart gFaces

getSymCtrl :: IState TreeView
getSymCtrl = getStatePartDbg "getSymCtrl" symCtrl

getAxiomCtrl :: IState TreeView
getAxiomCtrl = getStatePartDbg "getAxiomCtrl"  axiomCtrl

getPath :: IState GoBack
getPath  = getStatePartDbg "getPath" $ pathExpr . fromJust . gExpr

getStatus :: IState (Statusbar, ContextId)
getStatus  = getStatePartDbg "getStatus" status

getAxiomBox :: IState HBox
getAxiomBox = getStatePartDbg "getAxiomBox" $ axiomBox . fromJust . gProof



{- Las dos funciones que siguen devuelven cada uno de los panes; toda la 
   gracia está en getParentNamed. -}

-- | Retorna la caja contenedora de los widget de operadores de pre-expresion.
getTreeOpBox :: IState VBox
getTreeOpBox = getFaces >>= \f -> liftIO (notebookGetNthPage f 1) >>= 
                 \(Just w) -> liftIO (containerGetChildren (castToBox w)) >>= 
                 \[_,w] -> liftIO (containerGetChildren (castToBox w)) >>= 
                 \[_,m,_] -> liftIO (containerGetChildren (castToContainer m)) >>= 
                 \[m,_] -> return $ castToVBox m

-- | Retorna la caja contenedora del árbol de tipado de una pre-expresion.
getTreeExprBox :: IState VBox
getTreeExprBox = getFaces >>= \f -> liftIO (notebookGetNthPage f 1) >>= 
                 \(Just w) -> liftIO (containerGetChildren (castToBox w)) >>= 
                 \[_,w] -> liftIO (containerGetChildren (castToBox w)) >>= 
                 \[_,_,m] -> return $ castToVBox m

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

getTheorems :: IState [Theorem]
getTheorems = getStatePart theorems
                 
                 
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
selectFrom eventTE eb = getTreeExpr >>= \(Just tExpr) ->
                case ( eventTE (mainExpr tExpr) == eb
                     , find (\te -> (eventTE te) == eb) (notOpExpr tExpr)
                     )
                of
                    (False,Nothing) -> return ()
                    (True,_) -> update (\gst -> gst {gExpr = Just $ mainExpr tExpr})
                    (_,Just se) -> update (\gst -> gst {gExpr = Just se })
    where 
        find' :: Maybe ExprState
        find' = undefined

-- | Actualiza el tipo de un operador en la expresión principal del árbol de
-- tipado, en base a una lista de focus y moves.
updateTypeOpInMainExprTree :: [(Focus, Move)] -> Type -> IState ()
updateTypeOpInMainExprTree fs t = getMainExprTree >>= \exprT ->
                                  updateMainExprTree exprT {fExpr = (setType fs t (fExpr exprT))}

-- | Actualiza el tipo de un atomo en la expresión principal del árbol de
-- tipado, en base a un exprState.
updateTypeAtomInMainExprTree :: ExprState -> Type -> IState ()
updateTypeAtomInMainExprTree es t = getMainExprTree >>= \exprT ->
                                    updateMainExprTree exprT 
                                                {fExpr = setAtomType 
                                                            (fExpr exprT)
                                                            (fst $ pathExpr es)
                                                            t}

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

updateMainExprTree :: ExprState -> IState ()
updateMainExprTree es = update (\gst -> gst {gTreeExpr = Just $ tExpr (gTreeExpr gst)})
    where tExpr :: (Maybe TreeExpr) -> TreeExpr
          tExpr Nothing = TreeExpr es [] []
          tExpr (Just te) = TreeExpr es (opExpr te) (notOpExpr te)

updateOpExprTree :: [[(Focus, Move)]] -> (Maybe [(Focus,Move)]) -> (Maybe Type) -> IState ()
updateOpExprTree fss Nothing Nothing = update (\gst -> gst {gTreeExpr = Just $ tExpr (gTreeExpr gst)})
    where tExpr :: (Maybe TreeExpr) -> TreeExpr
          tExpr (Just te) = TreeExpr (mainExpr te) 
                                     fss 
                                     (notOpExpr te)
updateOpExprTree fss (Just fs) (Just t) = (update (\gst -> gst {gTreeExpr = Just $ tExpr (gTreeExpr gst)}))
    where 
          fss' = deleteBy (\fs' -> \fs -> ((fst . unzip) fs') == ((fst . unzip) fs)) fs fss
          tExpr :: (Maybe TreeExpr) -> TreeExpr
          tExpr (Just te) = TreeExpr (mainExpr te) 
                                     fss 
                                     (notOpExpr te)

-- | Limpia el árbol de tipado del estado general.
cleanTreeExpr :: IState ()
cleanTreeExpr = update (\gst -> gst { gTreeExpr = Nothing}) >> 
                getSelectExpr >>= \(Just es) -> 
                updateTypeSelectType es TyUnknown


-- Añade una expresion y su respectivo boton a al arbol de tipado.
addMainExprToTree :: Focus -> Type -> GoBack -> HBox -> HBox -> IState ExprState
addMainExprToTree f t p be bt = 
                    update (\gst@(GState _ _ (Just gte) _ _ _ _ _ _ _ _ _) -> 
                    gst { gTreeExpr = Just $ gte {mainExpr = te}}) >> return te
    where te :: ExprState
          te = ExprState { fExpr = f
                         , fType = t
                         , pathExpr = p
                         , eventExpr = be
                         , eventType = bt
                         }
                         
-- Funcion que chequea si la prueba en la interfaz está validada
checkValidProof :: IState Bool
checkValidProof = getProof >>= \pf ->
                  return (toProof pf) >>= \pr ->
                  liftIO (putStrLn ("la prueba es " ++ show pr)) >>
                  getValidProof >>= \vp ->
                  liftIO (putStrLn ("la prueba valida es " ++ show vp))  >>
                  case vp of
                       Left _ -> return False
                       Right p -> return (p==pr)

-- | Actualiza el tipo de la expresión principal del árbol de tipado.
updateMainExprTreeType :: Type -> IState ()
updateMainExprTreeType t =  getMainExprTree >>= \eTree ->
                            update (\gst@(GState _ _ (Just gte) _ _ _ _ _ _ _ _ _) -> 
                            gst { gTreeExpr = Just $ gte {mainExpr = te eTree t }})
    where te :: ExprState -> Type ->  ExprState
          te es t = es { fType = t }

-- | Añade un exprState a la lista de NO-operadores del árbol de tipado.
addNotOpExprTree :: ExprState -> IState ()
addNotOpExprTree es =  getNotOpExprTree >>= \l ->
                       update (\gst@(GState _ _ (Just gte) _ _ _ _ _ _ _ _ _) -> 
                       gst { gTreeExpr = Just $ gte {notOpExpr =  es : l}})

getMainExprTree :: IState ExprState
getMainExprTree = askRef >>= return . mainExpr . fromJust . gTreeExpr

getOpExprTree :: IState [[(Focus, Move)]]
getOpExprTree = askRef >>= return . opExpr . fromJust . gTreeExpr

getNotOpExprTree :: IState [ExprState]
getNotOpExprTree = askRef >>= return . notOpExpr . fromJust . gTreeExpr

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
