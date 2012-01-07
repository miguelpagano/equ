{-# Language OverloadedStrings #-}
-- | Aspectos de la interfaz relacionados con expresiones.
module Equ.GUI.Expr where

import Equ.GUI.Types
import Equ.GUI.Utils
import Equ.GUI.Settings
import Equ.GUI.Widget

import Equ.Expr
import Equ.PreExpr
import Equ.Syntax
import Equ.Parser
import Equ.Types

import Graphics.UI.Gtk hiding (eventButton, eventSent,get)
import Graphics.UI.Gtk.Gdk.EventM
import Data.Text (unpack)
import Control.Monad.Trans(lift,liftIO)
import Control.Monad.State(get)
import Control.Arrow((***))

-- | Devuelve la expresión que se estaba construyendo y empieza
-- una nueva construcción.
newExpr :: HBox -> IState PreExpr
newExpr b = clearFocus b >>= \e ->
            getFormPane >>= 
            openFormPane b >>
            return e

-- | Comienza la construcción de una nueva expresión.
clearFocus :: HBox -> IState PreExpr
clearFocus b = getExpr >>= \e -> 
               updateFocus emptyExpr (id,id) >> 
               showExpr >>
               updateFrmCtrl b >>
               clearExpr b >>
               (return . toExpr) e

-- | Limpia el contenido de una caja y pone el widget correspondiente
-- para ingresar una nueva expresión en esa caja. En el estado sólo
-- se actualiza la expresión del foco.
clearExpr :: HBox -> IRG
clearExpr b = removeAllChildren b >>
              setupForm b >> 
              liftIO (widgetShowAll b)

-- | Poné la representación de una expresión en una caja de texto.
-- Podría ser útil si queremos que se pueda transformar la expresión
-- que está siendo construida en algo que el usuario pueda editar 
-- como una string.
exprInEntry :: Syntactic t => Entry -> t -> IState ()
exprInEntry entry = liftIO . entrySetText entry . repr


-- TODO: manejar errores del parser.
-- Ale: Empece a hacer algo, lo principal es que muestra el error (no se rompe),
--      faltaría definirle forma y color.
-- | Dada una caja de texto, parsea el contenido como una expresión
-- y construye un widget con toda la expresión.
setExprFocus :: Entry -> HBox -> IRG
setExprFocus entry box = liftIO (entryGetText entry) >>= \s ->
                         case parseFromString s of
                            Right expr -> (updateExpr expr >>
                                            writeExprWidget expr box)
                            Left err -> 
                                   setErrMessage (show err) >>
                                    liftIO (widgetShowAll box) >>
                                    return ()
                                    
writeExprWidget :: PreExpr -> HBox -> IRG
writeExprWidget expr box =  frameExp expr >>= \(WExpr box' _) ->
                            removeAllChildren box >>
                            addToBox box box' >>
                            liftIO (widgetShowAll box)

typedExprEdit :: HBox -> IState ()
typedExprEdit b = getSelectExpr >>= \res ->
                    case res of
                            Nothing -> reportErrWithErrPaned 
                                                "Ninguna expresion seleccionada."
                            Just te -> return (fExpr te) >>= \(expr,_) ->
                                       newExpr b >>
                                       updateExpr expr >>
                                       frameExp expr >>= \(WExpr b' _) ->
                                       removeAllChildren b >>
                                       addToBox b b' >>
                                       liftIO (widgetShowAll b)

-- | Esta es la función principal: dada una expresión, construye un
-- widget con la expresión.
frameExp :: PreExpr -> IState (WExpr HBox)
{-
Esto es como estaba antes; el problema de esto es que necesitabámos
otra familia para no poner entry boxes en cada hueco.

frameExp e@(PrExHole h) = newBox >>= \box ->
                          newEntry >>= \entry ->
                          exprInEntry entry h >>
                          setupFormEv box entry >> 
                          return (WExpr box e)
-}
frameExp e@(PrExHole h) = newBox >>= \box -> setupForm box >>
                          return (WExpr box e)

frameExp e@(Var v) = newBox >>= \box ->
                     (labelStr . repr) v >>= \lblVar ->
                     setupFormEv box lblVar e >> 
                     return (WExpr box e)

frameExp e@(Con c) = newBox >>= \box ->
                     (labelStr . repr) c >>= \lblConst ->
                     setupFormEv box lblConst e >> 
                     return (WExpr box e)

frameExp e@(Fun f) = newBox >>= \box ->
                     (labelStr . repr) f >>= \lblConst ->
                     setupFormEv box lblConst e >> 
                     return (WExpr box e)

frameExp e@(UnOp op e') = newBox >>= \box ->
                          localPath (goDown,goUp) (frameExp e') >>= \(WExpr box' _) ->
                          (labelStr . repr) op >>= \lblOp ->
                          setupFormEv box lblOp e >>
                          setupFormEv box box' e >>
                          return (WExpr box e)

frameExp e@(BinOp op e1 e2) = newBox >>= \box ->
                              localPath (goDown,goUp)  (frameExp e1) >>= \(WExpr box1 _) ->
                              localPath (goDownR,goUp) (frameExp e2) >>= \(WExpr box2 _) ->
                              (labelStr . repr) op >>= \lblOp ->
                              addToBox box box1 >>
                              setupFormEv box lblOp e >>
                              addToBox box box2 >>
                              return (WExpr box e)

frameExp e@(App e1 e2) = newBox >>= \box ->
                           localPath (goDown,goUp) (frameExp e1) >>= \(WExpr box1 _) ->
                           localPath (goDownR,goUp) (frameExp e2) >>= \(WExpr box2 _) ->
                           labelStr  " " >>= \lblEnd ->
                           addToBox box box1 >>
                           setupFormEv box lblEnd e >>
                           addToBox box box2 >>
                           return (WExpr box e)


-- Este caso tiene un hack medio feo; nos fijamos en el texto de
-- variable para ver si la construimos nosotros o no.
frameExp e@(Quant q v e1 e2) = newBox >>= \box ->
                               getPath >>= \p ->
                               quantVar v p >>= \vbox ->
                               localPath (goDown,goUp)  (frameExp e1) >>= \(WExpr box1 _) ->
                               localPath (goDownR,goUp) (frameExp e2) >>= \(WExpr box2 _) ->
                               labelStr (qInit ++ (unpack $ tRepr q)) >>= \lblQnt ->
                               labelStr ":" >>= \lblRng ->
                               labelStr ":" >>= \lblTrm -> 
                               labelStr qEnd >>= \lblEnd ->
                               setupFormEv box lblQnt e >>
                               addToBox box vbox  >>
                               setupFormEv box lblRng e >>
                               addToBox box box1 >>
                               setupFormEv box lblTrm e >>
                               addToBox box box2 >>
                               setupFormEv box lblEnd e >>
                               return (WExpr box e)
    where 
        quantVar :: Variable -> GoBack -> IState HBox
        quantVar v p = newBox >>= \box ->
                       if isPlaceHolderVar v
                       then entryvar box p >> return box
                       else lblVar box v p >> return box
                     
        entryvar box p = newEntry >>= \entry ->
                         liftIO (set entry [ entryEditable := True ]) >>
                         withState (onEntryActivate entry) 
                           (liftIO (entryGetText entry) >>=
                                   return . parserVar >>=
                                   either (reportErrWithErrPaned . show) 
                                           (\v -> replaceEntry box v p >>
                                                 updateQVar v p >>
                                                 showExpr >>
                                                 return ())) >>
                         entryDim entry entryVarLength >>
                         addToBox box entry >>
                         liftIO (widgetShowAll box)

        replaceEntry b v p = removeAllChildren b >> lblVar b v p

        lblVar b v p = (labelStr . repr) v >>= \lblVar -> 
                       liftIO eventBoxNew >>= \eb ->
                       addToBox b eb >>
                       liftIO (set eb [ containerChild := lblVar ]) >>                    
                       addToBox b eb >>
                       get >>= \s ->
                       addHandler eb buttonPressEvent (editVar b s p) >>
                       liftIO (widgetShowAll b)                           

        editVar b s p = do RightButton <- eventButton
                           eventWithState (removeAllChildren b >>
                                           quantVar placeHolderVar p >>=
                                           addToBox b >>
                                           showExpr >>
                                           liftIO (widgetShowAll b)) s 
                           return ()

        qInit :: String
        qInit = quantInit equLang
        qEnd :: String
        qEnd = quantEnd equLang

frameExp e@(Paren e') = newBox >>= \box ->
                        localPath (goDown,goUp) (frameExp e') >>= \(WExpr box1 _) ->
                        labelStr "[" >>= \lblOpen ->
                        labelStr "]" >>= \lblClose -> 
                        setupFormEv box lblOpen e >>
                        addToBox box box1 >>
                        setupFormEv box  lblClose e >>
                        return (WExpr box e)

{- Las siguientes funciones construyen expresiones con huecos a partir de
un constructor de la sintáxis. -}

-- | Operadores.
writeOperator :: Operator -> HBox -> IRG
writeOperator o box = expOp o >>= \(WExpr b e) ->
                      updateExpr e >>
                      addToBox box b >>
                      liftIO (widgetShowAll box)

    where expOp o = case opNotationTy o of
                      NPrefix -> frameExp $ UnOp o holePreExpr
                      NPostfix -> frameExp $ UnOp o holePreExpr
                      NInfix -> frameExp $ BinOp o holePreExpr holePreExpr

-- | Cuantificadores.
writeQuantifier :: Quantifier -> HBox -> IRG
writeQuantifier q box = frameExp (Quant q 
                                  placeHolderVar
                                  (preExprHole "")
                                  (preExprHole "")) >>= \(WExpr b e) ->
                        updateExpr e >>
                        addToBox box b >>
                        liftIO (widgetShowAll box)

-- | Constantes.
writeConstant :: Constant -> HBox -> IRG
writeConstant c box = liftIO (putStrLn "writeConstant called") >>
                      updateExpr (Con c) >>
                      (labelStr . unpack . tRepr) c >>= \label ->
                      setupFormEv box label (Con c) >>
                      liftIO (widgetShowAll box)

-- | Pone una caja de texto para ingresar una expresión; cuando se
-- activa (presionando Enter) parsea el texto de la caja como una
-- expresión y construye el widget correspondiente.
writeExpr :: HBox -> IRG
writeExpr box = newEntry >>= \entry -> 
                getPath >>= \p ->
                withState (onEntryActivate entry) 
                              (localInPath p (setExprFocus entry box)) >>
                removeAllChildren box >>
                addToBox box entry >>
                liftIO (widgetGrabFocus entry >>
                        widgetShowAll box)

class ExpWriter s where
    writeExp :: s -> HBox -> IRG

instance ExpWriter Quantifier where
    writeExp s cont = removeAllChildren cont >> 
                      writeQuantifier s cont 
    
instance ExpWriter Operator where
    writeExp s cont = removeAllChildren cont >>
                      writeOperator s cont

instance ExpWriter Constant where
    writeExp s cont = removeAllChildren cont >>
                      writeConstant s cont 
