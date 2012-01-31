{-# Language OverloadedStrings, DoRec #-}
-- | Aspectos de la interfaz relacionados con expresiones.
module Equ.GUI.Expr where

import Equ.GUI.Types hiding (GState)
import Equ.GUI.Utils
import Equ.GUI.State
import Equ.GUI.Settings
import Equ.GUI.Widget
import Equ.GUI.TypeTree
-- import Equ.GUI.TT

import Equ.Expr
import Equ.PreExpr hiding (goDown,goUp,goDownR)
import qualified Equ.PreExpr as PE
import Equ.Syntax
import Equ.Parser
import Equ.Types

import qualified Graphics.UI.Gtk as G (get)
import Graphics.UI.Gtk hiding (eventButton, eventSent,get)
import Graphics.UI.Gtk.Gdk.EventM
import Data.Text (unpack)
import Data.Maybe (fromJust)
import Control.Monad.Trans(lift,liftIO)
import Control.Monad.State(evalStateT, get)
import Control.Monad.Reader
import Control.Arrow((***))

import qualified Data.Foldable as F


fromJust' = maybe (error "localPath...") id
goDownR = fromJust' . PE.goDownR
goDown = fromJust' . PE.goDown
goUp = fromJust' . PE.goUp

-- | Poné en una caja el widget que usamos para construir nuevas
-- expresiones.
setupForm ::  HBox -> EditMask -> IExpr ()
setupForm b emask p = io (setToolTip b "Doble click para ingresar una expresión") >>
                      labelStr emptyLabel >>= \l -> 
                      setupFormEv b l holePreExpr emask p

-- | Asigna los manejadores de eventos para widgets de expresiones a 
-- los controles.
setupFormEv :: WidgetClass w => HBox -> w -> PreExpr -> EditMask -> IExpr ()
setupFormEv b c e emask p = liftIO eventBoxNew >>= \eb ->
                            addToBox b eb >>
                            liftIO (set eb [ containerChild := c ]) >>
                            setupEvents b eb e emask p

-- | Define los manejadores de eventos para una caja que tiene el
-- widget para construir expresiones.
setupEvents :: WidgetClass w => HBox -> w -> PreExpr -> EditMask -> IExpr ()
setupEvents b eb e emask p = get >>= \s ->
                             getSymCtrl >>= \sym ->
                             addHandler eb enterNotifyEvent (highlightBox b hoverBg) >>
                             addHandler eb leaveNotifyEvent (unlightBox b Nothing) >>
                             addHandler eb buttonPressEvent (editExpr p b s sym) >>= 
                             \c -> case emask of
                                    Editable -> return ()
                                    NotEditable -> io $ signalDisconnect c

-- | Si apretamos el botón derecho, entonces editamos la expresión
-- enfocada.
editExpr :: Move -> HBox -> GRef -> IconView -> EventM EButton ()
editExpr p b s sym = do LeftButton <- eventButton
                        DoubleClick <- eventClick
                        eventWithState (newFocusToSym b p sym >> 
                                        getFocusedExpr p >>= \(e,_) ->
                                        writeExpr (Just e) b p) s
                        liftIO $ widgetShowAll b
                        return ()

-- | Pone una caja de texto para ingresar una expresión; cuando se
-- activa (presionando Enter) parsea el texto de la caja como una
-- expresión y construye el widget correspondiente.
writeExpr :: Maybe PreExpr -> HBox -> IExpr ()
writeExpr pre box p = newEntry >>= \entry -> 
                      F.mapM_ (exprInEntry entry) pre >>
                       withState (onEntryActivate entry) (setExprFocus entry box p) >>
                       removeAllChildren box >>
                       addToBox box entry >>
                       io (widgetGrabFocus entry >>  widgetShowAll box)


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
setExprFocus :: Entry -> HBox -> IExpr ()
setExprFocus entry box p = io (entryGetText entry) >>= \s ->
                           if null s 
                           then updateExpr hole p >> writeExprWidget hole box p
                           else case parseFromString s of
                                  Right expr -> updateExpr expr p >>
                                               writeExprWidget expr box p
                                  Left err -> 
                                      setErrMessage (show err) >>
                                      liftIO (widgetShowAll box) >>
                                      return ()
    where hole = preExprHole ""

writeExprWidget :: PreExpr -> HBox -> IExpr ()
writeExprWidget = writeExprWidget' Editable

writeExprTreeWidget :: PreExpr -> HBox -> IExpr ()
writeExprTreeWidget =  writeExprWidget' NotEditable

writeExprWidget' :: EditMask -> PreExpr -> HBox -> IExpr ()
writeExprWidget' emask expr box p = frameExp expr emask p >>= \(WExpr box' _) ->
                                    removeAllChildren box >>
                                    addToBox box box' >>
                                    io (widgetShowAll box)


-- | Esta es la función principal: dada una expresión, construye un
-- widget con la expresión.
frameExp :: PreExpr -> EditMask -> IExpr (WExpr HBox)
frameExp e@(PrExHole h) emask p = newBox >>= \box -> setupForm box emask p >>
                                  return (WExpr box e)

frameExp e@(Var v) emask p = newBox >>= \box ->
                             (labelStr . repr) v >>= \lblVar ->
                             setupFormEv box lblVar e emask p >> 
                             return (WExpr box e)

frameExp e@(Con c) emask p = newBox >>= \box ->
                             (labelStr . repr) c >>= \lblConst ->
                             setupFormEv box lblConst e emask p >> 
                             return (WExpr box e)

frameExp e@(Fun f) emask p = newBox >>= \box ->
                             (labelStr . repr) f >>= \lblConst ->
                             setupFormEv box lblConst e emask p >> 
                             return (WExpr box e)

frameExp e@(UnOp op e') emask p = newBox >>= \box ->
                                  localPath (goDown . p) (frameExp e' emask) >>= \(WExpr box' _) ->
                                  (labelStr . repr) op >>= \lblOp ->
                                  setupFormEv box lblOp e emask p >>
                                  setupFormEv box box' e emask p >>
                                  return (WExpr box e)

frameExp e@(BinOp op e1 e2) emask p = newBox >>= \box ->
                                      localPath (goDown . p)  (frameExp e1 emask) >>= \(WExpr box1 _) ->
                                      localPath (goDownR . p) (frameExp e2 emask) >>= \(WExpr box2 _) ->
                                      (labelStr . repr) op >>= \lblOp ->
                                      addToBox box box1 >>
                                      setupFormEv box lblOp e emask p >>
                                      addToBox box box2 >>
                                      return (WExpr box e)

frameExp e@(App e1 e2) emask p = newBox >>= \box ->
                                 localPath (goDown . p) (frameExp e1 emask) >>= \(WExpr box1 _) ->
                                 localPath (goDownR . p) (frameExp e2 emask) >>= \(WExpr box2 _) ->
                                 labelStr  " " >>= \lblEnd ->
                                 addToBox box box1 >>
                                 setupFormEv box lblEnd e emask p >>
                                 addToBox box box2 >>
                                 return (WExpr box e)


-- Este caso tiene un hack medio feo; nos fijamos en el texto de
-- variable para ver si la construimos nosotros o no.
frameExp e@(Quant q v e1 e2) emask p = newBox >>= \box ->
                                       quantVar v p >>= \vbox ->
                                       localPath (goDown . p)  (frameExp e1 emask) >>= \(WExpr box1 _) ->
                                       localPath (goDownR . p) (frameExp e2 emask) >>= \(WExpr box2 _) ->
                                       labelStr (qInit ++ (unpack $ tRepr q)) >>= \lblQnt ->
                                       labelStr ":" >>= \lblRng ->
                                       labelStr ":" >>= \lblTrm -> 
                                       labelStr qEnd >>= \lblEnd ->
                                       setupFormEv box lblQnt e emask p >>
                                       addToBox box vbox  >>
                                       setupFormEv box lblRng e emask p >>
                                       addToBox box box1 >>
                                       setupFormEv box lblTrm e emask p >>
                                       addToBox box box2 >>
                                       setupFormEv box lblEnd e emask p >>
                                       return (WExpr box e)
    where 
        quantVar :: Variable -> Move -> IState HBox
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

frameExp e@(Paren e') emask p = newBox >>= \box ->
                                localPath goDown (frameExp e' emask) >>= \(WExpr box1 _) ->
                                labelStr "[" >>= \lblOpen ->
                                labelStr "]" >>= \lblClose -> 
                                setupFormEv box lblOpen e emask p >>
                                addToBox box box1 >>
                                setupFormEv box  lblClose e emask p >>
                                return (WExpr box e)

{- Las siguientes funciones construyen expresiones con huecos a partir de
un constructor de la sintáxis. -}

-- | Operadores.
writeOperator :: Operator -> HBox -> IExpr ()
writeOperator o box p = expOp o >>= \(WExpr b e) ->
                        updateExpr e p >>
                        addToBox box b >>
                        liftIO (widgetShowAll box)

    where expOp o = case opNotationTy o of
                      NPrefix -> frameExp (UnOp o holePreExpr) Editable p
                      NPostfix -> frameExp (UnOp o holePreExpr) Editable p
                      NInfix -> frameExp (BinOp o holePreExpr holePreExpr) Editable p

-- | Cuantificadores.
writeQuantifier :: Quantifier -> HBox -> IExpr ()
writeQuantifier q box p = frameExp (Quant q 
                                    placeHolderVar
                                    (preExprHole "")
                                    (preExprHole "")) Editable p >>= \(WExpr b e) ->
                          updateExpr e p >>
                          addToBox box b >>
                          liftIO (widgetShowAll box)

-- | Constantes.
writeConstant :: Constant -> HBox -> IExpr ()
writeConstant c box p = updateExpr (Con c) p >>
                        (labelStr . unpack . tRepr) c >>= \label ->
                        setupFormEv box label (Con c) Editable p >>
                        liftIO (widgetShowAll box)


class ExpWriter s where
    writeExp :: s -> HBox -> IExpr ()

instance ExpWriter Quantifier where
    writeExp s cont p = removeAllChildren cont >> 
                        writeQuantifier s cont p
    
instance ExpWriter Operator where
    writeExp s cont p = removeAllChildren cont >>
                        writeOperator s cont p

instance ExpWriter Constant where
    writeExp s cont p = removeAllChildren cont >>
                        writeConstant s cont p

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

moveWin w = windowGetPosition w >>= \(x,y) ->
            windowMove w (x+64) (y+64)

typeTreeWindow :: IState Focus -> (Focus -> IState ()) -> Window -> ExprWidget -> IExpr Window
typeTreeWindow isf fmp w expr_w p = io (popupWin w) >>= \pop -> 
                       io (vBoxNew False 0) >>= \bTree -> 
                       io (hBoxNew False 0) >>= \we -> 
                       isf >>= \f ->
                       writeExprTreeWidget (fst f) we p >>
                       buildTreeExpr isf fmp bTree we expr_w p >>
                       io (containerAdd pop bTree) >>
                       return pop

makeOptionEvent :: Window -> ToggleButton -> String -> (ToggleButton -> Window -> IExpr ()) -> IExpr ()
makeOptionEvent  win tb s f p = io makeButtonBox >> f tb win p 
    where
        makeButtonBox :: IO ToggleButton
        makeButtonBox = imageNewFromStock s IconSizeMenu >>=
                        containerAdd tb >>
                        return tb

configAnnotTB :: (String -> IO ()) -> ToggleButton -> Window -> IExpr ()
configAnnotTB act tb w p = io $ actTBOn tb w (io . annotWindow act)                    

configTypeTreeTB :: IState Focus -> (Focus -> IState ()) -> ExprWidget -> ToggleButton ->  Window -> 
                    IExpr ()
configTypeTreeTB isf fmp expr_w tb w p = get >>= \s ->
                            io (actTBOn tb w $ \w' -> evalStateT (typeTreeWindow isf fmp w' expr_w p) s) >>
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
                              moveWin pop >>
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

-- | Crea un widget para una expresión. El argumento indica si es inicial.
-- En ese caso no se crea el botón para ver posibles reescrituras.
createExprWidget :: Bool -> IState ExprWidget
createExprWidget initial = do
    boxExpr <- io $ hBoxNew False 2    
    formBox <- io $ hBoxNew False 2

    choices <- if not initial
              then do
                exprChoices <- io $ makeButtonWithImage stockIndex
                io $ setToolTip exprChoices "Expresiones posibles"
                return . Just $ exprChoices
              else return Nothing
    
    exprButtons <- io hButtonBoxNew
    bAnnot <- io toggleButtonNew
    bType <- io toggleButtonNew
    bInfo <- exprStatus

    io (containerAdd exprButtons bAnnot  >>
        containerAdd exprButtons bType >>
        containerAdd exprButtons bInfo >>
        boxPackStart boxExpr exprButtons PackNatural 10 >>
        boxPackStart boxExpr formBox PackGrow 1 >>
       --        widgetSetSizeRequest boxExpr (-1) 50
        return ()
       )
           
    return $ ExprWidget { formBox = formBox
                        , extBox = boxExpr
                        , choicesButton = choices
                        , annotButton = bAnnot
                        , typeButton = bType
                        , imgStatus = bInfo
                        }

    where exprStatus :: IState Image
          exprStatus = io $ imageNewFromStock stockInfo IconSizeMenu

-- Funciones para la expresiones inicial.
createInitExprWidget :: PreExpr -> IExpr (HBox,HBox)
createInitExprWidget expr p = do
  
    expr_w <- eventsInitExprWidget expr p

    writeExprWidget expr (formBox expr_w) p    

    return (extBox expr_w , formBox expr_w)

-- | Setea los eventos del widget de la expresion inicial.
eventsInitExprWidget :: PreExpr -> IExpr ExprWidget 
eventsInitExprWidget expr p = do
    s <- get
    win <- getWindow

    expr_w <- createExprWidget False

    setupOptionExprWidget win expr_w p

    setupForm (formBox expr_w) Editable p 
    io $ widgetShowAll (extBox expr_w)
    return expr_w

setupOptionExprWidget :: Window -> ExprWidget -> IExpr ()
setupOptionExprWidget win expr_w p = do
  makeOptionEvent win (annotButton expr_w) stockEdit (configAnnotTB putStrLn) p
  io $ setToolTip (annotButton expr_w) "Anotaciones"
  makeOptionEvent win (typeButton expr_w) stockIndex (configTypeTreeTB (getExpr) (\(e,_) -> updateExpr e p) expr_w) p
  io $ setToolTip (typeButton expr_w) "Árbol de tipado"
    

loadExpr :: HBox -> PreExpr -> IExpr HBox 
loadExpr box expr p = do
    removeAllChildren box
    (exprBox,formBox) <- createInitExprWidget expr p
    io $ boxPackStart box exprBox PackNatural 2
    return formBox
            
reloadExpr :: HBox -> PreExpr -> IExpr ()
reloadExpr formBox expr p = removeAllChildren formBox >>
                            setupForm formBox Editable p >>
                            writeExprWidget expr formBox p

                        
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

