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

import Graphics.UI.Gtk hiding (eventButton, eventSent,get)
import Graphics.UI.Gtk.Gdk.EventM
import Data.Text (unpack)
import Control.Monad.Trans(lift,liftIO)


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
               updateFrmCtrl b >>
               clearExpr b >>
               (return . toExpr) e

-- | Limpia el contenido de una caja y pone el widget correspondiente
-- para ingresar una nueva expresión en esa caja. En el estado sólo
-- se actualiza la expresión del foco.
clearExpr :: HBox -> IRExpr
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
setExprFocus :: Entry -> HBox -> IRExpr
setExprFocus entry box = liftIO (entryGetText entry) >>= \s ->
                         case parseFromString s of
                            Right expr -> (updateExpr expr >>
                                            frameExp expr >>= \(WExpr box' _) ->
                                            removeAllChildren box >>
                                            addToBox box box' >>
                                            liftIO (widgetShowAll box))
                            Left err -> 
                                    getErrPanedLabel >>=
                                    \l -> liftIO (labelSetMarkup l 
                                                    (markSpan 
                                                    [ FontBackground "#FF0000"
                                                    , FontForeground "#000000"
                                                    ] 
                                                    (show err))) >>
                                    openErrPane >>
                                    liftIO (widgetShowAll box) >>
                                    return ()

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
                     setupFormEv box lblVar >> 
                     return (WExpr box e)

frameExp e@(Con c) = newBox >>= \box ->
                     (labelStr . repr) c >>= \lblConst ->
                     setupFormEv box lblConst >> 
                     return (WExpr box e)

frameExp e@(UnOp op e') = newBox >>= \box ->
                          localPath (goDown,goUp) (frameExp e') >>= \(WExpr box' _) ->
                          (labelStr . repr) op >>= \lblOp ->
                          setupFormEv box lblOp  >>
                          setupFormEv box box' >>
                          return (WExpr box e)

frameExp e@(BinOp op e1 e2) = newBox >>= \box ->
                              localPath (goDown,goUp)  (frameExp e1) >>= \(WExpr box1 _) ->
                              localPath (goDownR,goUp) (frameExp e2) >>= \(WExpr box2 _) ->
                              (labelStr . repr) op >>= \lblOp ->
                              addToBox box box1 >>
                              setupFormEv box lblOp >>
                              addToBox box box2 >>
                              return (WExpr box e)

frameExp e@(App e1 e2) = newBox >>= \box ->
                           localPath (goDown,goUp) (frameExp e1) >>= \(WExpr box1 _) ->
                           localPath (goDownR,goUp) (frameExp e2) >>= \(WExpr box2 _) ->
                           labelStr  " " >>= \lblEnd ->
                           addToBox box box1 >>
                           setupFormEv box lblEnd >>
                           addToBox box box2 >>
                           return (WExpr box e)


-- Este caso tiene un hack medio feo; nos fijamos en el texto de
-- variable para ver si la construimos nosotros o no.
frameExp e@(Quant q v e1 e2) = newBox >>= \box ->
                               quantVar v >>= \vbox ->
                               localPath (goDown,goUp)  (frameExp e1) >>= \(WExpr box1 _) ->
                               localPath (goDownR,goUp) (frameExp e2) >>= \(WExpr box2 _) ->
                               labelStr (quantInit ++ (unpack $ tRepr q)) >>= \lblQnt ->
                               labelStr ":" >>= \lblRng ->
                               labelStr ":" >>= \lblTrm -> 
                               labelStr quantEnd >>= \lblEnd ->
                               setupFormEv box lblQnt >>
                               addToBox box vbox  >>
                               setupFormEv box lblRng >>
                               addToBox box box1 >>
                               setupFormEv box lblTrm >>
                               addToBox box box2 >>
                               setupFormEv box lblEnd >>
                               return (WExpr box e)
    where quantVar :: Variable -> IState HBox
          quantVar v = if isPlaceHolderVar v
                       then entryvar 
                       else frameExp (Var v) >>= \(WExpr box _) ->
                            return box

          -- TOOD: hacer que si tenemos éxito parseando la variable, entonces
          -- la caja de texto se cambie por un label.
          entryvar = newEntry >>= \entry ->
                     liftIO (set entry [ entryEditable := True ]) >>
                     withState (onEntryActivate entry) 
                               (liftIO (entryGetText entry) >>=
                                       updateQVar) >>
                     entryDim entry entryVarLength >>
                     newBox >>= \box -> 
                     addToBox box entry >> return box


frameExp e@(Paren e') = newBox >>= \box ->
                        localPath (goDown,goUp) (frameExp e') >>= \(WExpr box1 _) ->
                        labelStr "[" >>= \lblOpen ->
                        labelStr "]" >>= \lblClose -> 
                        setupFormEv box lblOpen >>
                        addToBox box box1 >>
                        setupFormEv box  lblClose >>
                        return (WExpr box e)

frameExp e = (liftIO . putStrLn . show) e >> newBox >>= \b' -> return $ WExpr b' e

{- Las siguientes funciones construyen expresiones con huecos a partir de
un constructor de la sintáxis. -}

-- | Operadores.
writeOperator :: Operator -> HBox -> IRExpr
writeOperator o box = expOp o >>= \(WExpr b e) ->
                      updateExpr e >>
                      addToBox box b >>
                      liftIO (widgetShowAll box)

    where expOp o = case opNotationTy o of
                      NPrefix -> frameExp $ UnOp o holeExpr
                      NPostfix -> frameExp $ UnOp o holeExpr
                      NInfix -> frameExp $ BinOp o holeExpr holeExpr

-- | Cuantificadores.
writeQuantifier :: Quantifier -> HBox -> IRExpr
writeQuantifier q box = frameExp (Quant q 
                                  placeHolderVar
                                  (preExprHole "")
                                  (preExprHole "")) >>= \(WExpr b e) ->
                        updateExpr e >>
                        addToBox box b >>
                        liftIO (widgetShowAll box)

-- | Constantes.
writeConstant :: Constant -> HBox -> IRExpr
writeConstant c box = updateExpr (Con c) >>
                      (labelStr . unpack . tRepr) c >>= \label ->
                      setupFormEv box label >>
                      liftIO (widgetShowAll box)

-- | Pone una caja de texto para ingresar una expresión; cuando se
-- activa (presionando Enter) parsea el texto de la caja como una
-- expresión y construye el widget correspondiente.
writeExpr :: HBox -> IRExpr
writeExpr box = newEntry >>= \entry -> 
                withState (onEntryActivate entry) (setExprFocus entry box) >>
                removeAllChildren box >>
                addToBox box entry >>
                liftIO (widgetGrabFocus entry >>
                        widgetShowAll box)
    

class ExpWriter s where
    writeExp :: s -> HBox -> IRExpr

instance ExpWriter Quantifier where
    writeExp s cont = removeAllChildren cont >> 
                      writeQuantifier s cont 
    
instance ExpWriter Operator where
    writeExp s cont = removeAllChildren cont >>
                      writeOperator s cont

instance ExpWriter Constant where
    writeExp s cont = removeAllChildren cont >>
                      writeConstant s cont 

