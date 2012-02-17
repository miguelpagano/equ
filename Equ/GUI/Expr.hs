{-# Language DoAndIfThenElse, OverloadedStrings, DoRec #-}
-- | Aspectos de la interfaz relacionados con expresiones.
module Equ.GUI.Expr where

import Equ.GUI.Types hiding (GState)
import Equ.GUI.Utils
import Equ.GUI.State
import Equ.GUI.State.Expr
import Equ.GUI.Settings
import Equ.GUI.Widget
import Equ.GUI.TypeTree

import Equ.Expr
import qualified Equ.Proof as P
import qualified Equ.Proof.Proof as PP
import Equ.PreExpr hiding (goDown,goUp,goDownR)
import qualified Equ.PreExpr as PE
import Equ.Syntax
import Equ.Parser
import Equ.Types

import qualified Graphics.UI.Gtk as G (get)
import Graphics.UI.Gtk hiding (eventButton, eventSent,get, UpdateType)
import Graphics.UI.Gtk.Gdk.EventM
import Data.Text (unpack,pack)
import Data.Maybe (fromJust)
import Control.Monad.Reader
import Control.Monad.Trans(lift)
import Control.Arrow((***))

import qualified Data.Foldable as F


fromJust' str = maybe (error ("localPath: " ++ str)) id
goDownR = fromJust' "downR" . PE.goDownR
goDown = fromJust' "down" . PE.goDown
goUp = fromJust' "up" . PE.goUp

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
setupEvents :: HBox -> EventBox -> PreExpr -> EditMask -> IExpr' ()
setupEvents b eb e emask = lift get >>= \s ->
                           localBox b (
                             ask >>= \ env ->
                             lift (addHandler eb enterNotifyEvent (highlightBox b hoverBg)) >>
                             lift (addHandler eb leaveNotifyEvent (unlightBox b Nothing)) >>
                             -- manejamos evento "button release" para que se propague al padre
                             io (b `on` buttonPressEvent $ return False) >>
                             io (eb `on` buttonPressEvent $ return False) >>
                             lift (addHandler eb buttonPressEvent (editExpr b env s)) >>= 
                             \c -> case emask of
                                    Editable -> return ()
                                    NotEditable -> io $ signalDisconnect c
                                      )

-- | Si hacemos doble-click, entonces editamos la expresión enfocada.
editExpr :: HBox -> Env -> GRef -> EventM EButton ()
editExpr b env s = do LeftButton <- eventButton
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
                                      (runEnv (setExprFocus box entry) env) >>
                           removeAllChildren box >>
                           addToBox box entry) >>
                    -- manejamos evento "button release" para que se propague al padre
                     io (entry `on` buttonPressEvent $ return False) >>
                     io (widgetGrabFocus entry >> widgetShowAll box)

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
                                    localPath (goDown .) (frameExp e1 emask) >>= \(WExpr box1 _) ->
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
                                                 updateQVar v >>
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
configAnnotTB :: IState String -> (String -> IState ()) -> GRef -> Window -> IExpr' ()
configAnnotTB iST act s w = getAnnotButton >>= \tb ->
                      io $ setToolTip tb "Anotaciones" >>
                           actTBOn tb w (io . annotWindow iST act s)

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
annotWindow :: (IState String) -> (String -> IState ()) -> GRef -> Window -> IO Window
annotWindow iST act s w = popupWin w >>= \pop ->
                    hBoxNew False 1 >>= \b ->
                    annotBuffer iST s >>= \entry ->
                    boxPackStart b entry PackNatural 0 >>
                    containerAdd pop b >>
                    (pop `on` unrealize $ (G.get entry textViewBuffer >>= \buf ->
                                           G.get buf textBufferText >>= \str ->
                                           evalStateT (act str) s)) >>
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

annotBuffer :: IState String -> GRef -> IO TextView
annotBuffer iST s = 
            evalStateT iST s >>= \text ->
            textViewNew >>= \v ->
            textViewSetWrapMode v WrapWord >>
            textViewGetBuffer v >>= \b ->
            textBufferGetStartIter b >>= \startIter ->
            textBufferInsert b startIter text >>
            set v [widgetWidthRequest := 500, widgetHeightRequest := 300] >>
            return v

-- | Crea un widget para una expresión. El argumento indica si es inicial.
-- En ese caso no se crea el botón para ver posibles reescrituras.
createExprWidget :: Bool -> IState ExprWidget
createExprWidget initial = do

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
           
    return $ ExprWidget { formBox = formBox
                        , extBox = boxExpr
                        , choicesButton = choices
                        , annotButton = bAnnot
                        , typeButton = bType
                        , imgStatus = bInfo
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

    expr_w <- createExprWidget True
    flip runEnvBox (expr_w,p,ProofMove Just) $ 
         writeExprWidget (formBox expr_w) expr >>
         setupOptionInitExprWidget win
               
    return expr_w
    

setupOptionInitExprWidget :: Window -> IExpr' ()
setupOptionInitExprWidget win  = lift get >>= \gs ->
                                 configAnnotTB (return "") (io . putStrLn) gs win >> 
                                 configTypeTreeTB win

setupOptionExprWidget :: Window -> IExpr' ()
setupOptionExprWidget win  = ask >>= \env ->
                             lift get >>= \s ->
                             configAnnotTB (loadAnnotation env)
                                           (saveAnnotation env)
                                           s win >>
                             configTypeTreeTB win
    where
        loadAnnotation :: Env -> IState String
        loadAnnotation env = runReaderT (loadAnnot) env
        saveAnnotation :: Env -> String -> IState ()
        saveAnnotation env = flip runReaderT env . saveAnnot

-- | Carga la anotaci´on de una expresi´on en base al entorno.
loadAnnot :: IExpr' String
loadAnnot = ask >>= \env ->
            lift getProofAnnots >>= \p ->
            return $ getAnnot p env
    where
        getAnnot :: P.ProofFocusAnnots -> Env -> String
        getAnnot pfa env = getAnnotFromFocus $ pm (pme env) pfa
        getAnnotFromFocus :: Maybe P.ProofFocusAnnots -> String
        getAnnotFromFocus = unpack . fromJust . PP.getEnd . fst . fromJust

-- | Guarda la anotaci´on para una expresi´on en base al entorno.
saveAnnot :: String -> IExpr' ()
saveAnnot s = 
        ask >>= \env ->
        lift getProofAnnots >>= \p ->
        moveProofFocus p env >>= \pfa ->
        updateAnnot pfa
    where
        moveProofFocus :: P.ProofFocusAnnots -> Env -> IExpr' P.ProofFocusAnnots
        moveProofFocus pfa env = return . fromJust $ pm (pme env) pfa
        updateAnnot :: P.ProofFocusAnnots -> IExpr' ()
        updateAnnot pfa = lift $
            updateProofAnnots $ P.replace pfa $ P.updateEnd (fst pfa) (pack s)
            

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
  expr_w <- createExprWidget True
  -- Ponemos un ExprWidget sin sentido para iniciar el estado. ESTO PODRIA REVISARSE
  expr' <- newExprState expr expr_w hbox2
  updateExprState expr' 
