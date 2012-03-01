{-# Language DoAndIfThenElse, OverloadedStrings, DoRec #-}
-- | Aspectos de la interfaz relacionados con expresiones.
module Equ.GUI.Expr where

import Equ.GUI.Types hiding (GState)
import Equ.GUI.Utils
import Equ.GUI.State hiding (localPath,getExprWidget)
import Equ.GUI.State.Expr
import Equ.GUI.Settings
import Equ.GUI.Widget
import Equ.GUI.TypeTree

import Equ.Expr
import Equ.PreExpr hiding (goDown,goUp,goDownR)
import qualified Equ.PreExpr as PE
import Equ.Syntax
import Equ.Parser
import Equ.Types

import qualified Graphics.UI.Gtk as G (get)
import Graphics.UI.Gtk hiding (eventButton, eventSent,get, UpdateType)
import Graphics.UI.Gtk.Gdk.EventM
import Data.Text (unpack)
import Data.Maybe (fromJust)
import Control.Monad.Reader
import Control.Monad.Trans(lift)
import Control.Arrow((***))

import System.Random

import qualified Data.Foldable as F


fromJust' = maybe (error "localPath...") id
goDownR = fromJust' . PE.goDownR
goDown = fromJust' . PE.goDown
goUp = fromJust' . PE.goUp

-- | Poné en una caja el widget que usamos para construir nuevas
-- expresiones.
setupForm :: HBox -> EditMask -> IExpr' ()
setupForm box emask = io (setToolTip box "Doble click para ingresar una expresión") >>
                      lift (labelStr emptyLabel) >>= \l -> 
                      setupFormEv box l holePreExpr emask


-- | Asigna los manejadores de eventos para widgets de expresiones a 
-- los controles.
setupFormEv :: WidgetClass w => HBox -> w -> PreExpr -> EditMask -> IExpr' ()
setupFormEv b c e emask = io eventBoxNew >>= \eb ->
                          lift (addToBox b eb) >>
                          io (set eb [ containerChild := c ]) >>
                          setupEvents b eb e emask

-- | Define los manejadores de eventos para una caja que tiene el
-- widget para construir expresiones.
setupEvents :: WidgetClass w => HBox -> w -> PreExpr -> EditMask -> IExpr' ()
setupEvents b eb e emask = lift get >>= \s ->
                           ask >>= \ env ->
                           lift getSymCtrl >>= \sym ->
                           lift (addHandler eb enterNotifyEvent (highlightBox b hoverBg)) >>
                           lift (addHandler eb leaveNotifyEvent (unlightBox b Nothing)) >>
                           -- manejamos evento "button release" para que se propague al padre
                           io (b `on` buttonPressEvent $ return False) >>
                           io (eb `on` buttonPressEvent $ return False) >>
                           lift (addHandler eb buttonPressEvent (editExpr b env s sym)) >>= 
                           \c -> case emask of
                                  Editable -> return ()
                                  NotEditable -> io $ signalDisconnect c


-- | Si hacemos doble-click, entonces editamos la expresión enfocada.
editExpr :: HBox -> Env -> GRef -> IconView -> EventM EButton ()
editExpr b env s sym = do LeftButton <- eventButton
                          DoubleClick <- eventClick
                          flip eventWithState s $ 
                               flip runReaderT env $
                                    getPath >>= \p ->
                                    lift (getFocusedExpr p) >>= \(e,_) ->
                                    newFocusToSym >>                                              
                                    writeExpr (Just e) b
                          io $ widgetShowAll b

-- | Pone una caja de texto para ingresar una expresión; cuando se
-- activa (presionando Enter) parsea el texto de la caja como una
-- expresión y construye el widget correspondiente.
writeExpr :: Maybe PreExpr -> HBox -> IExpr' ()
writeExpr pre box = lift newEntry >>= \entry -> 
                    F.mapM_ (lift . exprInEntry entry) pre >>
                     ask >>= \env ->
                     lift (withState (onEntryActivate entry) 
                                      (runReaderT (setExprFocus box entry) env) >>
                           removeAllChildren box >>
                           addToBox box entry) >>
                    -- manejamos evento "button release" para que se propague al padre
                     io (entry `on` buttonPressEvent $ return False) >>
                     io (widgetGrabFocus entry >> widgetShowAll box)
    where isParent entry box = io $ widgetGetParent entry >>= \p -> 
                               case p of
                                 Nothing -> debug "entry no tiene padre"
                                 Just p' -> if castToHBox p'==box 
                                           then debug "el padre de entry es formBox"
                                           else debug "el padre de entry NO es formBox!"

-- | Poné la representación de una expresión en una caja de texto.
-- Podría ser útil si queremos que se pueda transformar la expresión
-- que está siendo construida en algo que el usuario pueda editar 
-- como una string.
exprInEntry :: Show t => Entry -> t -> IState ()
exprInEntry entry = io . entrySetText entry . show


-- TODO: manejar errores del parser.
-- Ale: Empece a hacer algo, lo principal es que muestra el error (no se rompe),
--      faltaría definirle forma y color.
-- | Dada una caja de texto, parsea el contenido como una expresión
-- y construye un widget con toda la expresión.
setExprFocus :: HBox -> Entry -> IExpr' ()
setExprFocus box entry  = io (entryGetText entry) >>= \s ->
                          getPath >>= \p ->
                          if null s 
                          then lift (updateExpr hole p) >> 
                               writeExprWidget box hole
                          else case parseFromString s of
                                 Right expr -> lift (updateExpr expr p) >>
                                              writeExprWidget box expr
                                 Left err -> lift (setErrMessage (show err)) >>
                                            io (widgetShowAll box)
    where hole = preExprHole ""

writeExprWidget :: HBox -> PreExpr ->  IExpr' ()
writeExprWidget = writeExprWidget' Editable

writeExprTreeWidget :: HBox -> PreExpr -> IExpr' ()
writeExprTreeWidget =  writeExprWidget' NotEditable

writeExprWidget' :: EditMask -> HBox -> PreExpr -> IExpr' ()
writeExprWidget' emask box expr = frameExp expr emask  >>= \(WExpr box' _) ->                              
                                  lift (removeAllChildren box >>
                                        addToBox box box') >>
                                  io (widgetShowAll box)


-- | Esta es la función principal: dada una expresión, construye un
-- widget con la expresión.
frameExp :: PreExpr -> EditMask -> IExpr' (WExpr HBox)
frameExp e@(PrExHole h) emask = lift newBox >>= \box -> 
                                setupForm box emask >>
                                return (WExpr box e)

frameExp e@(Var v) emask = lift newBox >>= \box ->
                           (lift . labelStr . repr) v >>= \lblVar ->
                           setupFormEv box lblVar e emask >> 
                           return (WExpr box e)

frameExp e@(Con c) emask = lift newBox >>= \box ->
                           (lift . labelStr . repr) c >>= \lblConst ->
                           setupFormEv box lblConst e emask >> 
                           return (WExpr box e)

frameExp e@(Fun f) emask = lift newBox >>= \box ->
                           (lift . labelStr . repr) f >>= \lblConst ->
                           setupFormEv box lblConst e emask >> 
                           return (WExpr box e)

frameExp e@(UnOp op e') emask = lift newBox >>= \box ->
                                localPath (goDown .) (frameExp e' emask) >>= \(WExpr box' _) ->
                                (lift . labelStr . repr) op >>= \lblOp ->
                                setupFormEv box lblOp e emask >>
                                setupFormEv box box' e emask >>
                                return (WExpr box e)

frameExp e@(BinOp op e1 e2) emask = lift newBox >>= \box ->
                                    localPath (goDown .)  (frameExp e1 emask) >>= \(WExpr box1 _) ->
                                    localPath (goDownR .) (frameExp e2 emask) >>= \(WExpr box2 _) ->
                                    (lift . labelStr . repr) op >>= \lblOp ->
                                    lift (addToBox box box1) >>
                                    setupFormEv box lblOp e emask >>
                                    lift (addToBox box box2) >>
                                    return (WExpr box e)

frameExp e@(App e1 e2) emask = lift newBox >>= \box ->
                               localPath (goDown .) (frameExp e1 emask) >>= \(WExpr box1 _) ->
                               localPath (goDownR .) (frameExp e2 emask) >>= \(WExpr box2 _) ->
                               lift (labelStr " ") >>= \lblApp ->
                               lift (addToBox box box1) >>
                               setupFormEv box lblApp e emask >>
                               lift (addToBox box box2) >>
                               return (WExpr box e)

-- Este caso tiene un hack medio feo; nos fijamos en el texto de
-- variable para ver si la construimos nosotros o no.
frameExp e@(Quant q v e1 e2) emask = lift newBox >>= \box ->
                                     getPath >>= \p ->
                                     lift (quantVar v p) >>= \vbox ->
                                     localPath (goDown .)  (frameExp e1 emask) >>= \(WExpr box1 _) ->
                                     localPath (goDownR .) (frameExp e2 emask) >>= \(WExpr box2 _) ->
                                     lift (labelStr (qInit ++ (unpack $ tRepr q))) >>= \lblQnt ->
                                     lift (labelStr ":") >>= \lblRng ->
                                     lift (labelStr ":") >>= \lblTrm -> 
                                     lift (labelStr qEnd) >>= \lblEnd ->
                                     setupFormEv box lblQnt e emask >>
                                     lift (addToBox box vbox)  >>
                                     setupFormEv box lblRng e emask >>
                                     lift (addToBox box box1) >>
                                     setupFormEv box lblTrm e emask >>
                                     lift (addToBox box box2) >>
                                     setupFormEv box lblEnd e emask >>
                                     return (WExpr box e)
    where 
        quantVar :: Variable -> Move -> IState HBox
        quantVar v p = newBox >>= \box ->
                       if isPlaceHolderVar v
                       then entryvar box p >> return box
                       else lblVar box v p >> return box
                     
        entryvar box p = newEntry >>= \entry ->
                         io (set entry [ entryEditable := True ]) >>
                         withState (onEntryActivate entry) 
                           (io (entryGetText entry) >>=
                                   return . parserVar >>=
                                   either (reportErrWithErrPaned . show) 
                                           (\v -> replaceEntry box v p >>
                                                 updateQVar v p >>
                                                 showExpr >>
                                                 return ())) >>
                         entryDim entry entryVarLength >>
                         addToBox box entry >>
                         io (widgetShowAll box)

        replaceEntry b v p = removeAllChildren b >> lblVar b v p

        lblVar b v p = (labelStr . repr) v >>= \lblVar -> 
                       io eventBoxNew >>= \eb ->
                       addToBox b eb >>
                       io (set eb [ containerChild := lblVar ]) >>                    
                       addToBox b eb >>
                       get >>= \s ->
                       addHandler eb buttonPressEvent (editVar b s p) >>
                       io (widgetShowAll b)                           

        editVar b s p = do RightButton <- eventButton
                           eventWithState (removeAllChildren b >>
                                           quantVar placeHolderVar p >>=
                                           addToBox b >>
                                           showExpr >>
                                           io (widgetShowAll b)) s 
                           return ()

        qInit :: String
        qInit = quantInit equLang
        qEnd :: String
        qEnd = quantEnd equLang

frameExp e@(Paren e') emask = lift newBox >>= \box ->
                              localPath (goDown .) (frameExp e' emask) >>= \(WExpr box1 _) ->
                              lift (labelStr "[") >>= \lblOpen ->
                              lift (labelStr "]") >>= \lblClose -> 
                              setupFormEv box lblOpen e emask >>
                              lift (addToBox box box1) >>
                              setupFormEv box  lblClose e emask >>
                              return (WExpr box e)

{- Las siguientes funciones construyen expresiones con huecos a partir de
un constructor de la sintáxis. -}

-- | Operadores.
writeOperator :: Operator -> HBox -> IExpr' ()
writeOperator o box = expOp o >>= \(WExpr b e) ->
                      getPath >>= \p ->
                      lift (updateExpr e p) >>
                      lift (addToBox box b) >>
                      io (widgetShowAll box)

    where expOp o = case opNotationTy o of
                      NPrefix ->  frameExp (UnOp o holePreExpr) Editable
                      NPostfix -> frameExp (UnOp o holePreExpr) Editable
                      NInfix ->   frameExp (BinOp o holePreExpr holePreExpr) Editable

-- | Cuantificadores.
writeQuantifier :: Quantifier -> HBox -> IExpr' ()
writeQuantifier q box  = frameExp (Quant q 
                               placeHolderVar
                               (preExprHole "")
                               (preExprHole "")) Editable >>= \(WExpr b e) ->
                         getPath >>= \p ->
                         lift (updateExpr e p) >>
                         lift (addToBox box b) >>
                         io (widgetShowAll box)

-- | Constantes.
writeConstant :: Constant -> HBox -> IExpr' ()
writeConstant c box  = getPath >>= \p ->
                       lift (updateExpr (Con c) p) >>
                       (lift . labelStr . unpack . tRepr) c >>= \label ->
                       setupFormEv box label (Con c) Editable >>
                       io (widgetShowAll box)


class ExpWriter s where
    writeExp :: s -> HBox -> IExpr' ()

instance ExpWriter Quantifier where
    writeExp s box = lift (removeAllChildren box) >>
                     writeQuantifier s box
    
instance ExpWriter Operator where
    writeExp s box = lift (removeAllChildren box) >>
                     writeOperator s box

instance ExpWriter Constant where
    writeExp s box = lift (removeAllChildren box) >>
                     writeConstant s box

popupWin :: Window -> IO Window
popupWin w = windowNew >>= \pop ->
             set pop  [ windowDecorated := False
                      , windowHasFrame := False
                      , windowTypeHint := WindowTypeHintDialog
                      , windowTransientFor := w
                      , windowGravity := GravityCenter
                      , windowOpacity := 0.8
                      ] >>
             windowSetPosition pop WinPosCenterAlways >>
             return pop

typeTreeWindow :: Window -> IExpr' Window
typeTreeWindow w = io (popupWin w) >>= \pop -> 
                   io (vBoxNew False 0) >>= \bTree -> 
                   io (hBoxNew False 0) >>= \we -> 
                   lift getExpr >>= \f ->
                   writeExprTreeWidget we (fst f)  >>
                   buildTreeExpr bTree we >>
                   io (containerAdd pop bTree) >>
                   return pop

-- | Pone el tooltip y configura la acciones para el boton de anotaciones 
-- del exprWidget.
configAnnotTB :: (String -> IO ()) -> Window -> IExpr' ()
configAnnotTB act w = getAnnotButton >>= \tb ->
                      io $ setToolTip tb "Anotaciones" >>
                           actTBOn tb w (io . annotWindow act)

-- | Pone el tooltip y configura la acciones para el boton del árbol
-- de tipado del exprWidget.
configTypeTreeTB :: Window -> IExpr' ()
configTypeTreeTB w = lift get >>= \s ->
                     getTypeButton >>= \tb ->
                     io (setToolTip tb "Árbol de tipado") >>
                     ask >>= \env ->
                     io (actTBOn tb w $ \w' -> flip evalStateT s $
                                     runReaderT (typeTreeWindow w') env) >>
                     return ()


-- | El primer argumento indica la acción a realizar con el contenido del 
-- buffer al momento de cerrar el popup.
annotWindow :: (String -> IO ()) -> Window -> IO Window
annotWindow act w = popupWin w >>= \pop ->
                    hBoxNew False 1 >>= \b ->
                    annotBuffer >>= \entry ->
                    boxPackStart b entry PackNatural 0 >>
                    containerAdd pop b >>
                    (pop `on` unrealize $ (G.get entry textViewBuffer >>= \buf ->
                                           G.get buf textBufferText >>=
                                           act)) >>
                    return pop


-- | Define la acción para cuando no está activado.
actTBOn :: ToggleButton -> Window -> (Window -> IO Window) -> IO ()
actTBOn tb w f = do rec {
                       cid <- tb `on` toggled $ io 
                             (f w >>= \pop ->
                              widgetShowAll pop >> 
                              windowPresent pop >>
                              signalDisconnect cid >>
                              actTBOff tb w f pop)
                    } ;
                    return ()

actTBOff :: ToggleButton -> Window -> (Window -> IO Window) -> Window -> IO ()
actTBOff tb w f pop = do rec {
                          cid <- tb `on` toggled $ io ( widgetDestroy pop >>
                                                       signalDisconnect cid >>
                                                       actTBOn tb w f)
                         }
                         return ()

annotBuffer :: IO TextView
annotBuffer = textViewNew >>= \v ->
             textViewSetWrapMode v WrapWord >>
             set v [widgetWidthRequest := 500, widgetHeightRequest := 300] >>
             return v

-- | Crea un widget para una expresión. El argumento "initial" indica si es inicial.
-- En ese caso no se crea el botón para ver posibles reescrituras.
-- El argumento "proofIndex" indica el paso de prueba en la cual este widget de expresion
-- se encuentra (a la derecha de tal paso).
createExprWidget :: Bool -> Int -> IState ExprWidget
createExprWidget initial proofIndex = do

    boxExpr <- io $ hBoxNew False 2    
    formBox <- io $ hBoxNew False 2

    choices <- if not initial
              then do
                exprChoices <- io $ makeButtonWithImage stockIndex
                io $ buttonSetRelief exprChoices ReliefNone >>
                     setToolTip exprChoices "Expresiones posibles"
                return . Just $ exprChoices
              else return Nothing

    bAnnot <- io $ makeButtonBox annotIcon
    bType <- io $ makeButtonBox typeTreeIcon
    bInfo <- io $ imageNewFromStock  (imgState Unknown) IconSizeMenu

    io $ do 
      boxPackStart boxExpr formBox PackGrow 2
      if not initial
      then boxPackStart boxExpr (fromJust choices) PackNatural 2
      else return ()
      boxPackStart boxExpr bInfo PackNatural 1 
      boxPackStart boxExpr bAnnot PackNatural 2
      boxPackStart boxExpr bType PackNatural 2
      widgetSetSizeRequest formBox 400 (-1)
           
    ran <- io $ randomIO
           
    return $ ExprWidget { formBox = formBox
                        , extBox = boxExpr
                        , choicesButton = choices
                        , annotButton = bAnnot
                        , typeButton = bType
                        , imgStatus = bInfo
                        , exprEventsIds = []
                        , exprProofIndex = proofIndex
                        , ewId = show (mod (ran :: Int) 200)
                        }

makeButtonBox :: String -> IO ToggleButton
makeButtonBox s = toggleButtonNew >>= \tb ->
                  imageNewFromStock s IconSizeSmallToolbar >>=
                  buttonSetImage tb >>
                  buttonSetImagePosition tb PosBottom >>
                  buttonSetRelief tb ReliefNone >>
                  return tb
                      
-- | Crea y setea los eventos del widget de la expresion inicial.
createInitExprWidget :: PreExpr -> IExpr ExprWidget 
createInitExprWidget expr p = do
    s <- get
    win <- getWindow

    expr_w <- createExprWidget True 0
    flip runReaderT (expr_w,p,0) $ 
         setupForm (formBox expr_w) Editable >>
         writeExprWidget (formBox expr_w) expr >>
         setupOptionExprWidget win
               
    return expr_w

setupOptionExprWidget :: Window -> IExpr' ()
setupOptionExprWidget win  = configAnnotTB putStrLn win >> 
                             configTypeTreeTB win


loadExpr :: HBox -> PreExpr -> IExpr ExprWidget 
loadExpr box expr p = do
    removeAllChildren box
    expr_w <- createInitExprWidget expr p
    io $ boxPackStart box (extBox expr_w) PackNatural 2
    io $ widgetShowAll (extBox expr_w)
    return expr_w
            
reloadExpr :: PreExpr -> IExpr' ()
reloadExpr expr = getFormBox >>= \box ->
                  lift (removeAllChildren box) >>
                  setupForm box Editable >>
                  writeExprWidget box expr


                        
newExprState :: Focus -> ExprWidget -> HBox -> IState ExprState
newExprState expr expr_w hbox2 = return $
                                 ExprState { fExpr = expr
                                           , fType = TyUnknown
                                           , eventType = hbox2
                                           , exprWidget = expr_w
                                           , formCtrl = formBox expr_w
                                           }                                 

initExprState expr = do 
  hbox2 <- io $ hBoxNew False 2
  expr_w <- createExprWidget True 0
  -- Ponemos un ExprWidget sin sentido para iniciar el estado. ESTO PODRIA REVISARSE
  expr' <- newExprState expr expr_w hbox2
  updateExprState expr' 
