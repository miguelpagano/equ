module Equ.GUI.State.TypeTree where

import Equ.GUI.Types
import Equ.GUI.State.Internal hiding (local)
import Equ.GUI.State.Proof
import Equ.GUI.State.Expr

import Equ.GUI.Utils
import Equ.Expr (Expr (..))
import Equ.PreExpr (Focus,toExpr, goTop)
import Equ.Proof(getStart, toProof)

import Graphics.UI.Gtk (HBox,ToggleButton,Image)

import Control.Monad.Reader
import Data.Maybe

import Equ.Expr
import Equ.PreExpr hiding(goUp,goRight,goLeft,goDown,goDownL)
import Equ.Theories
import Equ.Syntax
import Equ.Parser
import Equ.Exercise
import Equ.Rule
import Equ.Types

import Graphics.UI.Gtk hiding (eventButton, eventSent, get)

import Data.Text (unpack)
import Data.List

getTreeExpr :: IState (Maybe TreeExpr)
getTreeExpr = getStatePart gTreeExpr


selectExprFromBox :: HBox -> IState ()
selectExprFromBox = selectFrom (formCtrl)

selectTypeFromBox :: HBox -> IState ()
selectTypeFromBox = selectFrom (eventType)

selectFrom :: (ExprState -> HBox) -> HBox -> IState ()
selectFrom eventTE eb = getTreeExpr >>= \(Just tExpr) ->
                case ( eventTE (mainExpr tExpr) == eb
                     , find (\te -> (eventTE te) == eb) (atomExpr tExpr)
                     , find (\te -> (eventTE te) == eb) (quantExpr tExpr)
                     )
                of
                    (True,_,_) -> update (\gst -> gst {gExpr = Just $ mainExpr tExpr})
                    (_,Just se,_) -> update (\gst -> gst {gExpr = Just se })
                    (_,_,Just se) -> update (\gst -> gst {gExpr = Just se })
                    _ -> return ()

searchFocusInTree :: Focus -> IState [ExprState]
searchFocusInTree f = getTreeExpr >>= \(Just tExpr) ->
                case ( fExpr (mainExpr tExpr) == f
                     , filter (\te -> (fExpr te) == f) (atomExpr tExpr)
                     )
                of
                    (False, []) -> return ([mainExpr tExpr])
                    (True,_) -> return $ [mainExpr tExpr]
                    (_,ses) -> return $ ses

updateTypeQuantInExprTree :: ExprState -> Type -> IState ()
updateTypeQuantInExprTree es t = 
                        getTreeExpr >>= \(Just tExpr) ->
                        getQuantExprTree >>= \qETree ->
                        update (\gst -> gst {gTreeExpr = Just $
                                                tExpr {quantExpr = qETree' qETree} 
                                            })
    where qETree' :: [ExprState] -> [ExprState]
          qETree' les = map (\te -> if (eventType te) == (eventType es) 
                                        then te {fType = t}
                                        else te ) les

updateTypeAtomInExprTree :: ExprState -> Type -> IState ()
updateTypeAtomInExprTree es t = 
                        getTreeExpr >>= \(Just tExpr) ->
                        getAtomExprTree >>= \aETree ->
                        update (\gst -> gst {gTreeExpr = Just $
                                                tExpr {atomExpr = aETree' aETree} 
                                            })
    where aETree' :: [ExprState] -> [ExprState]
          aETree' les = map (\te -> if (eventType te) == (eventType es) 
                                        then te {fType = t}
                                        else te ) les

-- | Actualiza el tipo de un operador en la expresión principal del árbol de
-- tipado, en base a una lista de focus y moves.
updateTypeOpInMainExprTree :: [(Focus, Move)] -> Type -> IState ()
updateTypeOpInMainExprTree fs t = getMainExprTree >>= \exprT ->
                                  updateMainExprTree exprT {fExpr = (setType fs t (fExpr exprT))}

updateTypeQuantInMainExprTree :: ExprState -> Type -> IState ()
updateTypeQuantInMainExprTree es qt = getMainExprTree >>= \exprT ->
                                      updateMainExprTree exprT 
                                                {fExpr = setQuantType 
                                                            (fExpr exprT) id
                                                            qt}

updateTypeVarQInMainExprTree :: ExprState -> Type -> IState ()
updateTypeVarQInMainExprTree es qt = getMainExprTree >>= \exprT ->
                                      updateMainExprTree exprT 
                                                {fExpr = setVarQType 
                                                            (fExpr exprT) id
                                                            qt}


-- | Actualiza el tipo de un atomo en la expresión principal del árbol de
-- tipado, en base a un exprState.
updateTypeAtomInMainExprTree :: ExprState -> Type -> IState ()
updateTypeAtomInMainExprTree es t = getMainExprTree >>= \exprT ->
                                    updateMainExprTree exprT 
                                                {fExpr = setAtomType (fExpr exprT) id t}

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
updateMainExprTree es = updateMTT $ return . tExpr
    where tExpr :: (Maybe TreeExpr) -> TreeExpr
          tExpr Nothing = TreeExpr es [] [] []
          tExpr (Just te) = TreeExpr es (opExpr te) (atomExpr te) (quantExpr te)

updateOpExprTree :: [[(Focus, Move)]] -> (Maybe [(Focus,Move)]) -> (Maybe Type) -> IState ()
updateOpExprTree fss Nothing Nothing = updateMTT $ return . tExpr
    where tExpr :: (Maybe TreeExpr) -> TreeExpr
          tExpr (Just te) = TreeExpr (mainExpr te) 
                                     fss 
                                     (atomExpr te)
                                     (quantExpr te)
updateOpExprTree fss (Just fs) (Just t) = (update (\gst -> gst {gTreeExpr = Just $ tExpr (gTreeExpr gst)}))
    where 
          fss' = deleteBy (\fs' -> \fs -> ((fst . unzip) fs') == ((fst . unzip) fs)) fs fss
          tExpr :: (Maybe TreeExpr) -> TreeExpr
          tExpr (Just te) = TreeExpr (mainExpr te) 
                                     fss 
                                     (atomExpr te)
                                     (quantExpr te)

-- | Limpia el árbol de tipado del estado general.
cleanTreeExpr :: IState ()
cleanTreeExpr = updateMTT (const Nothing) >> 
                getExprState >>= \(Just es) -> 
                updateTypeSelectType es TyUnknown


-- | 
updateTT :: (TreeExpr -> TreeExpr) -> IState ()
updateTT f = askRef >>= \gst -> 
             case gTreeExpr gst of
               Just gte -> update $ \gst -> gst { gTreeExpr = return $ f gte }
               _ -> return ()

updateMTT :: (Maybe TreeExpr -> Maybe TreeExpr) -> IState ()
updateMTT f = askRef >>= \gst -> update $ \gst -> gst { gTreeExpr = f (gTreeExpr gst) }


-- | Actualiza el tipo de la expresión principal del árbol de tipado.
updateMainExprTreeType :: Type -> IState ()
updateMainExprTreeType t = getMainExprTree >>= \eTree ->
                           updateTT $ \gte -> gte {mainExpr = te eTree t }
    where te :: ExprState -> Type ->  ExprState
          te es t = es { fType = t }

-- | Añade un exprState a la lista de atomos del árbol de tipado.
addAtomExprTree :: ExprState -> IState ()
addAtomExprTree es = getAtomExprTree >>= \l ->
                     updateTT $ \gte -> gte {atomExpr = es:l}

-- | Añade un exprState a la lista de cuantificadores del árbol de tipado.
addQuantExprTree :: ExprState -> IState ()
addQuantExprTree es =  getQuantExprTree >>= \l ->
                       updateTT $ \gte -> gte {quantExpr = es:l}

getMainExprTree :: IState ExprState
getMainExprTree = getStatePartDbg "getMainExprTree" 
                                            (mainExpr . fromJust . gTreeExpr)

getOpExprTree :: IState [[(Focus, Move)]]
getOpExprTree = askRef >>= return . opExpr . fromJust . gTreeExpr

getAtomExprTree :: IState [ExprState]
getAtomExprTree = askRef >>= return . atomExpr . fromJust . gTreeExpr

getQuantExprTree :: IState [ExprState]
getQuantExprTree = askRef >>= return . quantExpr . fromJust . gTreeExpr

