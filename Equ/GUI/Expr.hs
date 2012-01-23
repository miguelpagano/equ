{-# Language OverloadedStrings, DoRec #-}
-- | Aspectos de la interfaz relacionados con expresiones.
module Equ.GUI.Expr where

import Equ.GUI.Types
import Equ.GUI.Utils
import Equ.GUI.State
import Equ.GUI.Settings
import Equ.GUI.Widget
import Equ.GUI.TypeTree

import Equ.Expr
import Equ.PreExpr
import Equ.Syntax
import Equ.Parser
import Equ.Types

import qualified Graphics.UI.Gtk as G (get)
import Graphics.UI.Gtk hiding (eventButton, eventSent,get)
import Graphics.UI.Gtk.Gdk.EventM
import Data.Text (unpack)
import Control.Monad.Trans(lift,liftIO)
import Control.Monad.State(evalStateT, get)
import Control.Arrow((***))

import qualified Data.Foldable as F

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
              setupForm b Editable >> 
              liftIO (widgetShowAll b)



-- | Poné en una caja el widget que usamos para construir nuevas
-- expresiones.
setupForm ::  HBox -> EditMask -> IRG
setupForm b emask = io (setToolTip b "Doble click para ingresar una expresión") >>
                   labelStr emptyLabel >>= \l -> setupFormEv b l holePreExpr emask

-- | Asigna los manejadores de eventos para widgets de expresiones a 
-- los controles.
setupFormEv :: WidgetClass w => HBox -> w -> PreExpr -> EditMask -> IRG
setupFormEv b c e emask = liftIO eventBoxNew >>= \eb ->
                    addToBox b eb >>
                    liftIO (set eb [ containerChild := c ]) >>
                    setupEvents b eb e emask

-- | Define los manejadores de eventos para una caja que tiene el
-- widget para construir expresiones.
setupEvents :: WidgetClass w => HBox -> w -> PreExpr -> EditMask -> IRG
setupEvents b eb e emask = get >>= \s ->
                     getPath >>= \p ->
                     getSymCtrl >>= \sym ->
                     addHandler eb enterNotifyEvent (highlightBox b hoverBg) >>
                     addHandler eb leaveNotifyEvent (unlightBox b Nothing) >>
                     addHandler eb buttonPressEvent (editExpr p b s sym) >>= 
                     \c -> case emask of
                                Editable -> return ()
                                NotEditable -> io $ signalDisconnect c

-- | Si apretamos el botón derecho, entonces editamos la expresión
-- enfocada.
editExpr :: GoBack -> HBox -> GRef -> IconView -> EventM EButton ()
editExpr p b s sym = do LeftButton <- eventButton
                        DoubleClick <- eventClick
                        eventWithState (newFocusToSym b p sym >> 
                                        updatePath p >> 
                                        getFocusedExpr >>= 
                                        flip writeExpr b . Just . fst) s
                        liftIO $ widgetShowAll b
                        return ()

-- | Pone una caja de texto para ingresar una expresión; cuando se
-- activa (presionando Enter) parsea el texto de la caja como una
-- expresión y construye el widget correspondiente.
writeExpr :: Maybe PreExpr -> HBox -> IRG
writeExpr pre box = newEntry >>= \entry -> 
                    F.mapM_ (exprInEntry entry) pre >>
                    getPath >>= \p ->
                    withState (onEntryActivate entry) 
                                  (localInPath p (setExprFocus entry box)) >>
                    removeAllChildren box >>
                    addToBox box entry >>
                    liftIO (widgetGrabFocus entry >>
                            widgetShowAll box)


-- | Poné la representación de una expresión en una caja de texto.
-- Podría ser útil si queremos que se pueda transformar la expresión
-- que está siendo construida en algo que el usuario pueda editar 
-- como una string.
exprInEntry :: Show t => Entry -> t -> IState ()
exprInEntry entry = liftIO . entrySetText entry . show


-- TODO: manejar errores del parser.
-- Ale: Empece a hacer algo, lo principal es que muestra el error (no se rompe),
--      faltaría definirle forma y color.
-- | Dada una caja de texto, parsea el contenido como una expresión
-- y construye un widget con toda la expresión.
setExprFocus :: Entry -> HBox -> IRG
setExprFocus entry box = liftIO (entryGetText entry) >>= \s ->
                         if null s 
                         then updateExpr hole >> writeExprWidget hole box
                         else case parseFromString s of
                                Right expr -> (updateExpr expr >>
                                              writeExprWidget expr box)
                                Left err -> 
                                    setErrMessage (show err) >>
                                    liftIO (widgetShowAll box) >>
                                    return ()
    where hole = preExprHole ""

writeExprWidget :: PreExpr -> HBox -> IRG
writeExprWidget = writeExprWidget' Editable

writeExprTreeWidget :: PreExpr -> HBox -> IRG
writeExprTreeWidget =  writeExprWidget' NotEditable

writeExprWidget' :: EditMask -> PreExpr -> HBox -> IRG
writeExprWidget' emask expr box =  frameExp expr emask >>= \(WExpr box' _) ->
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
                                       frameExp expr Editable >>= \(WExpr b' _) ->
                                       removeAllChildren b >>
                                       addToBox b b' >>
                                       liftIO (widgetShowAll b)

-- | Esta es la función principal: dada una expresión, construye un
-- widget con la expresión.
frameExp :: PreExpr -> EditMask -> IState (WExpr HBox)
{-
Esto es como estaba antes; el problema de esto es que necesitabámos
otra familia para no poner entry boxes en cada hueco.

frameExp e@(PrExHole h) = newBox >>= \box ->
                          newEntry >>= \entry ->
                          exprInEntry entry h >>
                          setupFormEv box entry >> 
                          return (WExpr box e)
-}
frameExp e@(PrExHole h) emask = newBox >>= \box -> setupForm box emask >>
                                return (WExpr box e)

frameExp e@(Var v) emask = newBox >>= \box ->
                     (labelStr . repr) v >>= \lblVar ->
                     setupFormEv box lblVar e emask >> 
                     return (WExpr box e)

frameExp e@(Con c) emask = newBox >>= \box ->
                     (labelStr . repr) c >>= \lblConst ->
                     setupFormEv box lblConst e emask >> 
                     return (WExpr box e)

frameExp e@(Fun f) emask = newBox >>= \box ->
                     (labelStr . repr) f >>= \lblConst ->
                     setupFormEv box lblConst e emask >> 
                     return (WExpr box e)

frameExp e@(UnOp op e') emask = newBox >>= \box ->
                          localPath (goDown,goUp) (frameExp e' emask) >>= \(WExpr box' _) ->
                          (labelStr . repr) op >>= \lblOp ->
                          setupFormEv box lblOp e emask >>
                          setupFormEv box box' e emask >>
                          return (WExpr box e)

frameExp e@(BinOp op e1 e2) emask = newBox >>= \box ->
                              localPath (goDown,goUp)  (frameExp e1 emask) >>= \(WExpr box1 _) ->
                              localPath (goDownR,goUp) (frameExp e2 emask) >>= \(WExpr box2 _) ->
                              (labelStr . repr) op >>= \lblOp ->
                              addToBox box box1 >>
                              setupFormEv box lblOp e emask >>
                              addToBox box box2 >>
                              return (WExpr box e)

frameExp e@(App e1 e2) emask = newBox >>= \box ->
                           localPath (goDown,goUp) (frameExp e1 emask) >>= \(WExpr box1 _) ->
                           localPath (goDownR,goUp) (frameExp e2 emask) >>= \(WExpr box2 _) ->
                           labelStr  " " >>= \lblEnd ->
                           addToBox box box1 >>
                           setupFormEv box lblEnd e emask >>
                           addToBox box box2 >>
                           return (WExpr box e)


-- Este caso tiene un hack medio feo; nos fijamos en el texto de
-- variable para ver si la construimos nosotros o no.
frameExp e@(Quant q v e1 e2) emask = newBox >>= \box ->
                               getPath >>= \p ->
                               quantVar v p >>= \vbox ->
                               localPath (goDown,goUp)  (frameExp e1 emask) >>= \(WExpr box1 _) ->
                               localPath (goDownR,goUp) (frameExp e2 emask) >>= \(WExpr box2 _) ->
                               labelStr (qInit ++ (unpack $ tRepr q)) >>= \lblQnt ->
                               labelStr ":" >>= \lblRng ->
                               labelStr ":" >>= \lblTrm -> 
                               labelStr qEnd >>= \lblEnd ->
                               setupFormEv box lblQnt e emask >>
                               addToBox box vbox  >>
                               setupFormEv box lblRng e emask >>
                               addToBox box box1 >>
                               setupFormEv box lblTrm e emask >>
                               addToBox box box2 >>
                               setupFormEv box lblEnd e emask >>
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

frameExp e@(Paren e') emask = newBox >>= \box ->
                        localPath (goDown,goUp) (frameExp e' emask) >>= \(WExpr box1 _) ->
                        labelStr "[" >>= \lblOpen ->
                        labelStr "]" >>= \lblClose -> 
                        setupFormEv box lblOpen e emask >>
                        addToBox box box1 >>
                        setupFormEv box  lblClose e emask >>
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
                      NPrefix -> frameExp (UnOp o holePreExpr) Editable
                      NPostfix -> frameExp (UnOp o holePreExpr) Editable
                      NInfix -> frameExp (BinOp o holePreExpr holePreExpr) Editable

-- | Cuantificadores.
writeQuantifier :: Quantifier -> HBox -> IRG
writeQuantifier q box = frameExp (Quant q 
                                  placeHolderVar
                                  (preExprHole "")
                                  (preExprHole "")) Editable >>= \(WExpr b e) ->
                        updateExpr e >>
                        addToBox box b >>
                        liftIO (widgetShowAll box)

-- | Constantes.
writeConstant :: Constant -> HBox -> IRG
writeConstant c box = updateExpr (Con c) >>
                      (labelStr . unpack . tRepr) c >>= \label ->
                      setupFormEv box label (Con c) Editable >>
                      liftIO (widgetShowAll box)

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

typeTreeWindow :: IState Focus -> (Focus -> IState ()) -> Window -> IState Window
typeTreeWindow isf fmp w = io (popupWin w) >>= \pop -> 
                       io (vBoxNew False 0) >>= \bTree -> 
                       io (hBoxNew False 0) >>= \we -> 
                       isf >>= \f ->
                       writeExprTreeWidget (fst f) we >>
                       buildTreeExpr isf fmp bTree we >>
                       io (containerAdd pop bTree) >>
                       return pop

makeOptionEvent :: Window -> String -> (ToggleButton -> Window -> IState ()) -> IState ToggleButton
makeOptionEvent win s f = io makeButtonBox >>= \tb -> f tb win >> return tb
    where
        makeButtonBox :: IO ToggleButton
        makeButtonBox = toggleButtonNew >>= \tb ->
                        imageNewFromStock s IconSizeMenu >>=
                        containerAdd tb >>
                        return tb

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

configAnnotTB :: (String -> IO ()) -> ToggleButton -> Window -> IState ()
configAnnotTB act tb w = io $ actTBOn tb w (io . annotWindow act)
               
configTypeTreeTB :: IState Focus -> (Focus -> IState ()) -> ToggleButton ->  Window -> IState ()
configTypeTreeTB isf fmp tb w = get >>= \s ->
                            io (actTBOn tb w $ \w' -> evalStateT (typeTreeWindow isf fmp w') s) >>
                            return ()

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


-- Funciones para la expresiones inicial.
createInitExprWidget :: PreExpr -> IState (HBox,HBox)
createInitExprWidget expr  = do
  
    boxExprWidget <- io $ hBoxNew False 2
    
    formBox <- io $ hBoxNew False 2
    --expr_choices <- io $ makeButtonWithImage stockIndex
    --io $ setToolTip expr_choices "Expresiones posibles"
    --button_box <- io $ hButtonBoxNew
    io (widgetSetSizeRequest boxExprWidget (-1) 50)
    
    eventsInitExprWidget expr boxExprWidget formBox
    
    writeExprWidget expr formBox
    
    return (boxExprWidget,formBox)
--     
-- | Setea los eventos de un widget de expresion. La funcion f es la
-- que se utiliza para actualizar la expresion dentro de la prueba
eventsInitExprWidget :: PreExpr -> HBox -> HBox -> IState ()
eventsInitExprWidget expr ext_box formBox =
    get >>= \s ->
    getWindow >>= \win ->
    setupOptionExprWidget win expr >>
    setupForm formBox Editable
    
    where setupOptionExprWidget :: Window -> PreExpr-> IState ()
          setupOptionExprWidget win e = do

            exprButtons <- io hButtonBoxNew

            bAnot <- makeOptionEvent win stockEdit (configAnnotTB putStrLn)
            io $ setToolTip bAnot "Anotaciones"
            bT    <- makeOptionEvent win stockIndex (configTypeTreeTB (getExpr)
                                            (\(e,_) -> updateExpr e))
            io $ setToolTip bT "Árbol de tipado"
            bInfo <- makeLayoutTypeCheckStatus

            io (containerAdd exprButtons bAnot  >>
                containerAdd exprButtons bT >>
                containerAdd exprButtons bInfo >>
                boxPackStart ext_box exprButtons PackNatural 10 >>
                boxPackStart ext_box formBox PackGrow 1 >>
                widgetShowAll ext_box)

          makeLayoutTypeCheckStatus :: IState Image
          makeLayoutTypeCheckStatus = io $ imageNewFromStock stockInfo IconSizeMenu


loadExpr :: HBox -> PreExpr -> IState HBox
loadExpr box expr = do
    removeAllChildren box
    (exprBox,formBox) <- createInitExprWidget expr
    io $ boxPackStart box exprBox PackNatural 2
    return formBox
            
reloadExpr :: HBox -> PreExpr -> IState ()
reloadExpr formBox expr = removeAllChildren formBox >>
                          setupForm formBox Editable >>
                          writeExprWidget expr formBox  

                        
newExprState :: Focus -> HBox -> HBox -> IState ExprState
newExprState expr hbox1 hbox2 = do
    return eState
    where 
        eState = ExprState { fExpr = expr
                           , pathExpr = (id,id)
                           , eventExpr = hbox1
                           , fType = TyUnknown
                           , eventType = hbox2
        }
                            

initExprState expr = do 
  hbox1 <- io $ hBoxNew False 2
  hbox2 <- io $ hBoxNew False 2
  expr' <- newExprState expr hbox1 hbox2
  updateExprState expr' 
