-- | Aspectos de la interfaz independientes de las expresiones.
module Equ.GUI.TypeTree (buildTreeExpr) where

import Equ.PreExpr
import Equ.Parser
import Equ.TypeChecker (checkPreExpr)
import Equ.Types

import Equ.GUI.Utils
import Equ.GUI.Widget
import Equ.GUI.Types
import Equ.GUI.State hiding (getExprWidget,localPath)
import Equ.GUI.State.Expr
import Equ.GUI.Settings

import Graphics.UI.Gtk hiding (get,UpdateType)

import Control.Monad.Reader
import Control.Monad (when, unless) 

import Data.List (find)
import qualified Data.Foldable as F

updateAtPlace = flip (updateExpr . fst)

-- | Construye la caja donde se muestra el árbol.
typeTreeWidget eb btree =  io $ do 
                             sep <- hSeparatorNew 
                             vb <- vBoxNew False 0
                             bb <- hBoxNew False 0
                             boxPackStart vb sep PackNatural 2
                             boxPackStart vb eb PackGrow 2
                             boxPackEnd bb vb PackGrow 2
                             boxPackEnd btree bb PackNatural 2
                             widgetShowAll bb


-- | Función principal que construye el arbol de tipado.
-- Esencialmente, esta función construye una caja donde se muestra el
-- arbol construido con @buildTreeExpr'@. 
buildTreeExpr :: VBox -> HBox -> IExpr' [(ExprState,Move)]
buildTreeExpr bTreeExpr we = do f <- lift getExpr
                                io $ debug $ show f
                                ws <- io (containerGetChildren we)
                                if (length ws < 1) 
                                then error "buildTreeExpr: unexpected short we"
                                else do 
                                  [we'] <- io (containerGetChildren we)
                                  p <- getPath
                                  mes <- makeMainExprState f (castToHBox we')
                                  typeTreeWidget (eventType mes) bTreeExpr
                                  -- Construye el árbol propiamente dicho.
                                  l <- buildTreeExpr' (castToHBox we') mes bTreeExpr
                                  -- Agrega la expresión en el extremo superior de la caja
                                  -- de tipado
                                  io $ boxPackStart bTreeExpr we PackGrow 5
                                  -- Configura los eventos en las hojas para poder editar los tipos.
                                  let l' = (mes,p):l --map (\(e,p') -> (e,p')) l
                                  configTypeEntry bTreeExpr l'
                                  return l'

    where makeMainExprState f we  = io (chkPreExp f) >>= \t -> 
                                    makeExprState f t we 

makeExprState :: Focus -> Type -> HBox -> IExpr' ExprState
makeExprState f t eb  = io (setupEventExpr f t eb) >>= \ev_type ->
                        getExprWidget >>= \ expr_w ->
                        return $ ExprState { fExpr = f
                                           , fType = t
                                           , eventType = ev_type
                                           , exprWidget = expr_w
                                           , formCtrl = eb
                                           }

                    
-- Función secundaria que contruye el árbol de tipado.
buildTreeExpr' :: HBox -> ExprState -> VBox -> IExpr' [(ExprState,Move)]
buildTreeExpr' we te bTree = do
            leftBranch  <- io $ goTypedExpr goDownL (fExpr te)
            rightBranch <- io $ goTypedExpr goDownR  (fExpr te)
            expr_w <- getExprWidget
            case (leftBranch, rightBranch) of
              (Just (lf, lt, lp), Just (rf, rt, rp)) -> do 
                  ws <- io (containerGetChildren we)                    
                  if length ws < 3 
                  then error "unexpected short ws in buildTreeExpr'"
                  else return ws >>= \[leb, _, reb] ->
                       makeExprState lf lt (castToHBox leb) >>= \dlte ->
                       makeExprState rf rt (castToHBox reb) >>= \drte ->
                    
                       io (hBoxNew False 0) >>= \bTree' ->
                       io (boxPackEnd bTree bTree' PackNatural 2) >>
                       io (fillNewBox bTree' rf (eventType drte)) >>= \nVbr ->
                       io (fillNewBox bTree' lf (eventType dlte)) >>= \nVbl ->

                       localPath (const rp) (buildTreeExpr' (castToHBox reb) drte nVbr) >>= \l' ->
                       localPath (const lp) (buildTreeExpr' (castToHBox leb) dlte nVbl) >>= \l'' ->
                       return ((dlte,lp):(drte,rp): (map (\(e,p') -> (e,p' . lp)) l'')
                                                   ++(map (\(e,p') -> (e,p' . rp)) l'))
                    
              (Just (lf, lt, lp), Nothing) -> do
                    -- manejo de expresiones con parentesis.
                    leb <- if isPreExprParent (fExpr te)
                          then do 
                            [_, eb, _] <- io $ containerGetChildren we
                            return eb
                          else do
                            [_, eb] <- io $ containerGetChildren we
                            [leb]   <- io $ containerGetChildren (castToEventBox eb)
                            return leb
            
                    dlte <- makeExprState lf lt (castToHBox leb)
                    
                    bTree' <- io $ hBoxNew False 0
                    io $ boxPackEnd bTree bTree' PackNatural 2
                    nVb <- io (fillNewBox bTree' lf (eventType dlte)) 
                    
                    l' <- localPath (const lp) (buildTreeExpr' (castToHBox leb) dlte nVb)
                    return ((dlte,lp):map (\(e,p') -> (e,p' . lp)) l')

              (Nothing,_) -> return []



-- | 
fillNewBox :: (BoxClass b) => b -> Focus -> HBox -> IO VBox
fillNewBox bTree f tb = vBoxNew False 0 >>= \nVb ->
                        boxPackEnd nVb tb PackNatural 2 >> 
                        when (not $ checkIsAtom f)
                             (io hSeparatorNew >>= \sep ->
                              boxPackEnd nVb sep PackNatural 2) >>
                        boxPackEnd bTree nVb PackGrow 2 >> 
                        widgetShowAll bTree >>
                        return nVb

paintBranchErr :: Focus -> [ExprState] -> IState ()
paintBranchErr f ess = F.mapM_ paint (find (\e -> fExpr e == f) ess)
    where paint :: ExprState -> IState ()
          paint es = highlightBox (eventType es) errBg >>
                     F.mapM_ (\f' -> paintBranchErr f' ess) (goUp f)

-- | Aplica el type-checker a la expresión seleccionada.
typedCheckType :: Focus -> [(ExprState,Move)] -> IState ()
typedCheckType f ess = either (\err -> paintBranchErr ((fst . fst) err) (map fst ess) >>
                                      (reportErrWithErrPaned $ show err))
                              (const $ return ())
                              (checkPreExpr (toExpr f))
--                         case unify checkedType (getTypeFocus f) emptySubst of
--                         Left err' -> reportErrWithErrPaned $ show err'
--                         Right _   -> undefined

-- | Define el manejador de eventos de la caja para editar typos.
setupEventsLeaf :: VBox -> (ExprState,Move) -> IExpr' ()
setupEventsLeaf extBTree (es,p') = do 
  let b = eventType es
  [tb'] <- io $ containerGetChildren b
  tb <- return $ castToEventBox tb'
  s <- get
  env <- ask
  io (tb `on` buttonPressEvent $ tryEvent $ flip eventWithState s $
         flip runReaderT env $
                  getPath >>= \p ->
                  lift getExpr >>=
                  return . show . getTypeFocus . p' . p . goTop >>= \ty ->
                  io entryNew >>= \eText ->
                  io (entrySetText eText ty >>
                      containerRemove b tb >>
                      boxPackStart b eText PackGrow 0 >> 
                      widgetShowAll b) >>
                  onTypeEdited eText extBTree b tb es p')
  return ()

-- | Manejo del evento Activate en las cajas de texto de tipos:
-- sólo se hace algo si el parseo es exitoso. Si el parseo falla,
-- el error se muestra en la función @checkInType@. Si el parseo
-- es exitoso, se elimina el entryBox y se pone una etiqueta.
onTypeEdited :: Entry -> VBox -> HBox -> EventBox -> ExprState -> Move -> IExpr' ()
onTypeEdited eText extBTree b tb es p' = ask >>= \ env -> 
            lift (withState (onEntryActivate eText) (flip runReaderT env $ 
                        lift getExpr >>= \f ->
                        io (entryGetText eText) >>= \text -> 
                        lift (checkInType text) >>= \checkText ->
                        flip F.mapM_ checkText (\t ->
                           io (labelNew $ Just $ show t) >>= \typeL -> 
                           io (containerGetChildren tb >>= \[oldL] ->
                               containerRemove tb oldL >> 
                               containerRemove b eText >> 
                               set tb [containerChild := typeL] >> 
                               set b [containerChild := tb] >> 
                               widgetShowAll b) >>
                        getPath >>= \p ->
                        lift (updateAtPlace (p' . p) (setAtomType f (p' . p . goTop) t)) >>
                        lift (getFocusedExpr p) >>= \(e,_) -> 
                        lift (updateExpr e p) >>
                        io (containerGetChildren extBTree) >>= \wl ->
                        io (containerRemove extBTree (head wl)) >>
                        lift (removeAllChildren extBTree) >>
                        return (castToHBox $ head wl) >>= \we ->
                        lift getExpr >>= \f' ->
                        buildTreeExpr extBTree we >>= \l ->
                        lift (typedCheckType f' l) >>
                        return ()))) >>
            return ()

-- | Aplica la función para transformar los labels de tipos
-- atómicos en entryBoxes para poder cambiarlos.
configTypeEntry :: VBox -> [(ExprState,Move)] -> IExpr' ()
configTypeEntry extBTree ess = mapM_ (\es ->  when ((checkIsAtom . fExpr) (fst es))
                                                          (setupEventsLeaf extBTree es)) ess

-- Configuración general para los botones. 
-- (Coloreo y desColoreo al pasar por encima)
setupHighlighting :: (BoxClass w) => EventBox -> w -> w -> IO ()
setupHighlighting eb exprB typeB = 
                        onEvent enterNotifyEvent (highlightBox exprB hoverBg) >>
                        onEvent leaveNotifyEvent (unlightBox exprB Nothing) >>
                        return ()
    where onEvent event action = eb `on` event $ tryEvent action

-- | Navega una expresión (la seleccionada) y devuelve, si se puede
-- hacer la navegación, una tripla con el foco, el tipo, y el
-- desplazamiento para llegar a ese lugar.
goTypedExpr :: (Focus -> Maybe Focus) -> Focus -> IO (Maybe (Focus, Type, Move))
goTypedExpr go te = case go te of
                      Nothing -> return Nothing
                      Just f ->  chkPreExp f >>= \t -> return (Just (f, t, fromJust' . go))
    where fromJust' = maybe (error "unexpected nothing at goTypedExpr") id

-- Setea el par expresión, tipo para construir el árbol de tipado.
setupEventExpr :: Focus -> Type -> HBox -> IO HBox
setupEventExpr (e,_) t exprEbb = do
                                typeL <- labelNew $ Just $ show t
                                typeEb <- eventBoxNew
                                typeEbb <- hBoxNew False 0
                                setupHighlighting typeEb exprEbb typeEbb
                                set typeEb  [ containerChild := typeL ]
                                set typeEbb [ containerChild := typeEb ]
                                return typeEbb

-- | Checkeo del tipo ingresado para la expresión.
checkInType :: String -> IState (Maybe Type)
checkInType s = case parseTyFromString s of
                     Left err -> reportErrWithErrPaned (show err) >> 
                                 return Nothing
                     Right t -> return $ Just t

chkPreExp :: Focus -> IO Type
chkPreExp = either (const $ return TyUnknown) return . checkPreExpr . fst

