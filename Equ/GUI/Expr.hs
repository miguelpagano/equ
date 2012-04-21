{-# Language DoAndIfThenElse, OverloadedStrings, DoRec #-}
-- | Aspectos de la interfaz relacionados con expresiones.
module Equ.GUI.Expr where

import Equ.GUI.Types hiding (GState)
import Equ.GUI.Utils
import Equ.GUI.State hiding (local)
import Equ.GUI.State.Expr 
import Equ.GUI.State.Exercise(showChoicesButton, getExercise, getExerciseConfTypeCheck)
import Equ.GUI.Settings
import Equ.GUI.Widget
import Equ.GUI.TypeTree

import Equ.Expr
import Equ.Exercise.Conf
import qualified Equ.Proof as P
import qualified Equ.Proof.Proof as PP
import Equ.Proof.Annot (ListedAnnots)
import Equ.Proof.ListedProof (getBasicAt,updateExprAt,getStartExpr
                             ,updateFirstExpr,getSelExpr
                             )
import Equ.PreExpr hiding (goDown,goUp,goDownR)
import qualified Equ.PreExpr as PE
import Equ.PreExpr.Eval
import qualified Equ.PreExpr.Show as PS
import Equ.Syntax
import Equ.Parser
import Equ.TypeChecker(checkPreExpr)
import Equ.Types

import qualified Graphics.UI.Gtk as G (get)
import Graphics.UI.Gtk hiding (eventButton, eventSent,get, UpdateType)
import Graphics.UI.Gtk.Gdk.EventM
import Data.Text (unpack,pack)
import Data.Maybe (fromJust,isJust)
import Control.Monad.Reader
import Control.Monad.Trans(lift)
import Control.Arrow((***),(&&&))

import System.Random

import qualified Data.Foldable as F

fromJust' str = maybe (error ("localPath: " ++ str)) id
goDownR = fromJust' "downR" . PE.goDownR
goDown = fromJust' "down" . PE.goDown
goUp = fromJust' "up" . PE.goUp

-- | Poné en una caja el widget que usamos para construir nuevas
-- expresiones.
setupForm :: HBox -> EditMask -> String -> IExpr' ()
setupForm box emask s = -- io (setToolTip box "Doble click para ingresar una expresión") >>
                      lift (labelStr $ emptyLabel s) >>= \l -> 
                      io fontItalic >>= \sf ->
                      io (widgetModifyFont l (Just sf)) >>
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
setupEvents b eb e emask = 
        lift get >>= \s ->
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
editExpr b env s = do 
        LeftButton <- eventButton
        click <- eventClick
        case click of
            DoubleClick -> flip eventWithState s $ 
                getSelIndexProof >>= \i ->
                io (debug $ 
                    "editando expresion con environment pme = "++ show i) >>
                (flip runReaderT (env {pme=i}) $ 
                    exprChangeStatus (ew env) NotParsed >>
                    getPath >>= \p ->
                    lift (getFocusedExpr p) >>= \f@(e,_) ->
                    io (debug $ "expresion seleccionada: " ++ show f) >>
                    newFocusToSym >>
                    writeExpr (Just f) b
                )
            SingleClick -> flip eventWithState s $ 
                getFocusAt >>= \(fi@(ei,_),ewi) ->
                updateExpr ei (mv env) >>
                findExprBox fi ewi >>= \focusB ->
                flip runReaderT (env {bx = focusB}) newFocusToSym >>
                lift (highlightBox focusB focusBg)
    where
        pairM :: (IState Focus, IState ExprWidget) -> IState (Focus, ExprWidget)
        pairM (mf,mew) = mf >>= \f -> mew >>= \ew -> return (f,ew)
        getP :: Int -> IState Focus
        getP i = getProof >>= \p -> return (mv env $ goTop $ getBasicAt i p)
        getPW :: Int -> IState ExprWidget
        getPW i = getProofWidget >>= \p -> return $ getBasicAt i p
        getFocusAt :: IState (Focus,ExprWidget)
        getFocusAt = do
                mi <- getIndexBasic (ew env)
                case mi of
                    Nothing -> io (debug $ "Indice single click: InitExpr") >>
                               getExpr >>= \f ->
                               getExprWidget >>= \ew ->
                               return (mv env $ goTop f,ew)
                    Just i -> io (debug $ "Indice single click: " ++ show i) >>
                              changeProofFocusAndShow i >>
                              pairM ((getP &&& getPW) i)

-- | Pone una caja de texto para ingresar una expresión; cuando se
-- activa (presionando Enter) parsea el texto de la caja como una
-- expresión y construye el widget correspondiente.
writeExpr :: Maybe Focus -> HBox -> IExpr' ()
writeExpr pre box = 
            lift newEntry >>= \entry -> 
            F.mapM_ (lift . exprInEntry entry) pre >>
            ask >>= \env ->
            lift (withState (onEntryActivate entry) 
                            (runEnv (setExprFocus box entry pre) env) >>
                get >>= \s ->
                io (entry `on` buttonReleaseEvent $ tryEvent $ 
                   (eventWithState (changeProofFocusAndShow (pme env)) s)) >>
                liftIO (debug "expr writed") >>
                removeAllChildren box >>
                addToBox box entry) >>
        -- manejamos evento "button release" para que se propague al padre
            io (entry `on` buttonPressEvent $ return False) >>
            io (widgetGrabFocus entry >> widgetShowAll box)
                     
-- | Poné la representación de una expresión en una caja de texto.
-- Podría ser útil si queremos que se pueda transformar la expresión
-- que está siendo construida en algo que el usuario pueda editar 
-- como una string.
exprInEntry :: Entry -> Focus -> IState ()
exprInEntry entry = io . entrySetText entry . (PS.showExpr) . fst

-- TODO: manejar errores del parser.
-- Ale: Empece a hacer algo, lo principal es que muestra el error (no se rompe),
--      faltaría definirle forma y color.
-- | Dada una caja de texto, parsea el contenido como una expresión
-- y construye un widget con toda la expresión.
setExprFocus :: HBox -> Entry -> Maybe Focus -> IExpr' ()
setExprFocus box entry (Just (_,path)) = 
                        io (entryGetText entry) >>= \s ->
                        if null s then putHole else parse s
    where hole :: PreExpr
          hole = preExprHole ""
          putHole :: IExpr' ()
          putHole = getPath >>= \p -> lift (updateExpr hole p) >> 
                    configExprStatus (hole,path) >>
                    writeExprWidget hole >> return ()
          parse :: String -> IExpr' ()
          parse s = liftIO (debug "parsing expr") >>
                    getPath >>= \p ->
                    case parseFromString s of
                        Right expr -> 
                            liftIO (debug "writing Expr:") >>
                            writeFocusWidget (expr,path) >> 
                            return ()
                        Left err -> 
                            lift (setErrMessage (show err)) >>
                            io (widgetShowAll box)

checkAndUpdateType :: Focus -> IExpr' ()
checkAndUpdateType f = lift getExercise >>= \exer ->
                       typeCheckConfigExpr (isJust exer) f >>= \e' ->
                       getPath >>= \p ->
                       lift (updateExpr e' p)

writeExprWidget :: PreExpr ->  IExpr' WExprList
writeExprWidget e = let f = toFocus e in
                        configExprStatus f >>
                        writeExprWidget' Editable Sugar Nothing f

writeFocusWidget :: Focus -> IExpr' WExprList
writeFocusWidget f = checkAndUpdateType f >>
                     writeExprWidget' Editable Sugar Nothing f

writeInitExprWidget :: PreExpr -> IExpr' WExprList
writeInitExprWidget e = let f = toFocus e in
                        configExprStatus f >>
                        writeExprWidget' NotEditable Sugar Nothing f

writeExprTreeWidget :: HBox -> PreExpr -> IExpr' WExprList
writeExprTreeWidget b e = writeExprWidget' NotEditable Kernel (Just b)$toFocus e

writeExprWidget' :: EditMask -> ViewMask -> (Maybe HBox) -> Focus -> 
                    IExpr' WExprList
writeExprWidget' emask vmask mhbox f@(e,_) = 
        ask >>= \env ->
        getBox mhbox >>= \box ->
        local (\env -> env {mv = id}) (frameExp (toExpr f) emask vmask) >>= 
        \wes -> lift (removeAllChildren box >> addToBox box (takeBox vmask wes)) >>
        io (widgetShowAll box) >>
        lift (safeGetProofWidget) >>= \mlpw ->
        ask >>= \env ->
        case (emask, mlpw) of
            (NotEditable,_) -> return wes
            (_,Nothing) -> lift getExprState >>= \(Just es) ->
                        updateEs es wes >>
                        return wes
            (_,Just lpw) -> (updateW wes lpw) >>= \uew ->
                            mUpdateExprAt (pme env) uew lpw >>= \ulpw ->
                            lift (updateProofWidget ulpw) >> 
                            return wes
    where
        upEs :: ExprState -> WExprList -> ExprState
        upEs es wes = (es {exprWidget = (exprWidget es) {wExprL = wes}})
        updateEs :: ExprState -> WExprList -> IExpr' ()
        updateEs es wes = lift . updateExprState $ upEs es wes
        getBox :: Maybe HBox -> IExpr' HBox
        getBox = maybe (ask >>= \env -> return (formBox $ ew env)) (return)
        mUpdateExprAt :: Int -> ExprWidget -> ListedProofWidget -> 
                         IExpr' ListedProofWidget
        mUpdateExprAt i e l = return $ updateExprAt i e l
        updateW :: WExprList -> ListedProofWidget -> IExpr' ExprWidget
        updateW wes lpw = return $ (getSelExpr lpw) {wExprL = wes}

frameExp :: PreExpr -> EditMask -> ViewMask -> IExpr' WExprList
frameExp e emask vmask = frameExp' (toFocus e) emask vmask emptyWExprList

-- | Esta es la función principal: dada una expresión, construye un
-- widget con la expresión.
frameExp' :: Focus -> EditMask -> ViewMask -> WExprList -> IExpr' WExprList
frameExp' f@(PrExHole h,_) emask vmask wes = 
                        lift newBox >>= \box -> 
                        setupForm box emask (unpack $ info h) >>
                        return (appendWExprList (WExpr Nothing (ctw box) f) wes)

frameExp' f@(e@(Var v),_) emask vmask wes = 
                        lift newBox >>= \box ->
                        (lift . labelStr . repr) v >>= \lblVar ->
                        setupFormEv box lblVar e emask >> 
                        return (appendWExprList (WExpr Nothing (ctw box) f) wes)

frameExp' f@(e@(Con c),_) emask vmask wes = 
                        lift newBox >>= \box ->
                        (lift . labelStr . repr) c >>= \lblConst ->
                        setupFormEv box lblConst e emask >> 
                        return (appendWExprList (WExpr Nothing (ctw box) f) wes)

frameExp' f@(e@(Fun fun),_) emask vmask wes = 
                        lift newBox >>= \box ->
                        (lift . labelStr . repr) fun >>= \lblConst ->
                        setupFormEv box lblConst e emask >> 
                        return (appendWExprList (WExpr Nothing (ctw box) f) wes)

frameExp' f@(e@(UnOp op e'),p) emask vmask wes =                
        let f1' = goDown f in
            lift newBox >>= \boxK ->
            createDownWidget f1' >>=
            \wes' -> (lift . labelStr . repr) op >>= 
            \lblOp -> setupFormEv boxK lblOp e emask >>
            setupFormEv boxK (takeBox vmask wes') e emask >>
            case evalNat e of
                Nothing -> return 
                           (appendWExprList (WExpr Nothing (ctw boxK) f) 
                                            (concatWExprList wes wes'))
                Just n -> lift newBox >>= \boxS ->
                        (lift . labelStr . show) n >>= \lblInt ->
                        setupFormEv boxS lblInt e emask >> 
                        return 
                        (appendWExprList (WExpr (Just $ ctw boxS) (ctw boxK) f) 
                                         (concatWExprList wes wes'))
    where createDownWidget f' =
            if parentNeeded f' op
               then localPath (goDown .) (frameExpWithFalseParens (goDown f) emask vmask wes)
               else localPath (goDown .) (frameExp' (goDown f) emask vmask wes)
               
          parentNeeded (e,_) op = case e of
                                       (BinOp _ _ _) -> True
                                       (App _ _) -> True
                                       (Quant _ _ _ _) -> True
                                       otherwise -> False

frameExp' f@(e@(BinOp op e1 e2),p) emask vmask wes =
    -- tenemos que ver si en e1 o en e2 hay que poner parentesis desambiguadores.
        let (f1',f2') = (goDown f,goDownR f) in
            lift newBox >>= \boxK ->
            
            createLeftWidget f1' >>= \leftwes ->
                        
            createRightWidget f2' >>= \rightwes ->
                        
            (lift . labelStr . repr) op >>= \lblOp ->
            lift (addToBox boxK (takeBox vmask leftwes)) >>
            setupFormEv boxK lblOp e emask >>
            lift (addToBox boxK (takeBox vmask rightwes)) >>
            case PS.showL e "" of 
                Nothing -> return (appendWExprList (WExpr Nothing (ctw boxK) f) 
                                  (concatWExprList wes $ 
                                            concatWExprList leftwes rightwes))
                Just list -> lift newBox >>= \boxS -> 
                             (lift . labelStr) list >>= \lblList ->
                             setupFormEv boxS lblList e emask >>
                             return 
                             (appendWExprList (WExpr (Just $ ctw boxS) (ctw boxK) f) 
                                  (concatWExprList wes $ 
                                            concatWExprList leftwes rightwes))
    where parentNeeded (e,_) op = case e of
                                    (BinOp op' _ _) -> if opPrec op >= opPrec op' 
                                                          then True
                                                          else False
                                    _ -> False
                                    
          createLeftWidget f1' =            
                if parentNeeded f1' op 
                    then localPath (goDown .) 
                            (frameExpWithFalseParens (goDown f) emask vmask wes)
                    else localPath (goDown .) 
                            (frameExp' (goDown f) emask vmask wes)
          
          createRightWidget f2' =
                if parentNeeded f2' op
                    then localPath (goDownR .) 
                                (frameExpWithFalseParens (goDownR f) emask vmask wes)
                    else localPath (goDownR .) 
                                (frameExp' (goDownR f) emask vmask wes)
          
                             
frameExp' f@(e@(App e1 e2),p) emask vmask wes = 
            lift newBox >>= \boxK ->
            localPath (goDown .) 
                (frameExp' (goDown f) emask vmask wes) >>= \leftwes ->
            localPath (goDownR .) 
                (frameExp' (goDownR f) emask vmask wes) >>= \rightwes ->
            lift (labelStr " ") >>= \lblApp ->
            lift (addToBox boxK (takeBox vmask leftwes)) >>
            setupFormEv boxK lblApp e emask >>
            lift (addToBox boxK (takeBox vmask rightwes)) >>
            return (appendWExprList (WExpr Nothing (ctw boxK) f) 
                                  (concatWExprList wes $ 
                                            concatWExprList leftwes rightwes))

-- Este caso tiene un hack medio feo; nos fijamos en el texto de
-- variable para ver si la construimos nosotros o no.
frameExp' f@(e@(Quant q v e1 e2),_) emask vmask wes = 
                lift newBox >>= \boxK ->
                getPath >>= \p ->
                lift (quantVar v p) >>= \vbox ->
                localPath (goDown .) 
                    (frameExp' (goDown f) emask vmask wes) >>= \leftwes ->
                localPath (goDownR .) 
                    (frameExp' (goDownR f) emask vmask wes) >>= \rightwes ->
                lift (labelStr (qInit ++ (unpack $ tRepr q))) >>= \lblQnt ->
                lift (labelStr ":") >>= \lblRng ->
                lift (labelStr ":") >>= \lblTrm -> 
                lift (labelStr qEnd) >>= \lblEnd ->
                setupFormEv boxK lblQnt e emask >>
                lift (addToBox boxK vbox)  >>
                setupFormEv boxK lblRng e emask >>
                lift (addToBox boxK (takeBox vmask leftwes)) >>
                setupFormEv boxK lblTrm e emask >>
                lift (addToBox boxK (takeBox vmask rightwes)) >>
                setupFormEv boxK lblEnd e emask >>
                return (appendWExprList (WExpr Nothing (ctw boxK) f) 
                                  (concatWExprList wes $ 
                                            concatWExprList leftwes rightwes))
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

frameExp' f@(e@(Paren e'),_) emask vmask wes = 
            lift newBox >>= \boxK ->
            localPath (goDown .) (frameExp' (goDown f) emask vmask wes) >>= \wes' ->
            lift (labelStr "(") >>= \lblOpen ->
            lift (setLabelColor lblOpen parenColor) >>
            lift (labelStr ")") >>= \lblClose -> 
            lift (setLabelColor lblClose parenColor) >>
            setupFormEv boxK lblOpen e emask >>
            lift (addToBox boxK (takeBox vmask wes')) >>
            setupFormEv boxK  lblClose e emask >>
            return (appendWExprList (WExpr Nothing (ctw boxK) f) 
                                    (concatWExprList wes wes'))
            
frameExpWithFalseParens f@(e,_) emask vmask wes =
            lift newBox >>= \boxK ->
            frameExp' f emask vmask wes >>= \wes' ->
            lift (labelStr "(") >>= \lblOpen ->
            --lift (setLabelColor lblOpen fakeParenColor) >>
            lift (labelStr ")") >>= \lblClose -> 
            --lift (setLabelColor lblClose fakeParenColor) >>
            setupFormEv boxK lblOpen e emask >>
            lift (addToBox boxK (takeBox vmask wes')) >>
            setupFormEv boxK  lblClose e emask >>
            return (appendWExprList (WExpr Nothing (ctw boxK) f) 
                                    (concatWExprList wes wes'))

{- Las siguientes funciones construyen expresiones con huecos a partir de
un constructor de la sintáxis. -}

-- | Operadores.
writeOperator :: Operator -> HBox -> IExpr' ()
writeOperator o box = getPath >>= \p ->
                      lift (getFocusedExpr p) >>= \(_,path) ->
                      lift (updateExpr expOp p) >>
                      writeFocusWidget (expOp, path) >>
                      return ()
    where 
        expOp :: PreExpr
        expOp = case opNotationTy o of
                      NPrefix ->  UnOp o holePreExpr
                      NPostfix -> UnOp o holePreExpr
                      NInfix ->   BinOp o holePreExpr holePreExpr

-- | Cuantificadores.
writeQuantifier :: Quantifier -> HBox -> IExpr' ()
writeQuantifier q box  = getPath >>= \p ->
                         lift (getFocusedExpr p) >>= \(_,path) ->
                         lift (updateExpr expQ p) >>
                         writeFocusWidget (expQ, path) >>
                         return ()
    where 
        expQ :: PreExpr
        expQ = Quant q placeHolderVar (preExprHole "") (preExprHole "")

-- | Constantes.
writeConstant :: Constant -> HBox -> IExpr' ()
writeConstant c box  = getPath >>= \p ->
                         lift (getFocusedExpr p) >>= \(_,path) ->
                         lift (updateExpr expCon p) >>
                         writeFocusWidget (expCon, path) >>
                         return ()
    where
        expCon :: PreExpr
        expCon = Con c

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

typeTreeWindow :: Window -> Bool -> IExpr' Window
typeTreeWindow w initial = 
                    io (popupWin w) >>= \pop -> 
                    io (vBoxNew False 0) >>= \bTree -> 
                    io (hBoxNew False 0) >>= \we -> 
                    (if initial then
                        lift getInitialExpr >>= \(Just (Expr e)) ->
                        io (debug $ "------------------> typeTreeWindow: " ++ show e)>>
                        writeExprTreeWidget we e >>= return
                    else
                        getProofMove >>= \idx ->
                        lift getProof >>= \prf ->
                        return (getBasicAt idx prf) >>= \f ->
                        writeExprTreeWidget we (toExpr f) >>=
                        return) >>= \wes ->
                    buildTreeExpr bTree we wes initial >>
                    io (containerAdd pop bTree) >>
                    return pop

-- | Pone el tooltip y configura la acciones para el boton de anotaciones 
-- del exprWidget.
configAnnotTB :: IState String -> (String -> IState ()) -> GRef -> Window -> 
                 IExpr' (ConnectId ToggleButton)
configAnnotTB iST act s w = getAnnotButton >>= \tb ->
                            io $ setToolTip tb "Anotaciones" >>
                            actTBOn tb w (io . annotWindow iST act s)

-- | Pone el tooltip y configura la acciones para el boton del árbol
-- de tipado del exprWidget.
configTypeTreeTB :: Window -> Bool -> IExpr' (ConnectId ToggleButton)
configTypeTreeTB w initial = lift get >>= \s ->
                     getTypeButton >>= \tb ->
                     io (setToolTip tb "Árbol de tipado") >>
                     ask >>= \env ->
                     io (actTBOn tb w $ \w' -> flip evalStateT s $
                                     runReaderT (typeTreeWindow w' initial) env)

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
actTBOn :: ToggleButton -> Window -> (Window -> IO Window) -> IO (ConnectId ToggleButton)
actTBOn tb w f = do rec {
                       cid <- tb `on` toggled $ io 
                             (f w >>= \pop ->
                              widgetShowAll pop >> 
                              windowPresent pop >>
                              signalDisconnect cid >>
                              actTBOff tb w f pop)
                    } ;
                    return cid

actTBOff :: ToggleButton -> Window -> (Window -> IO Window) -> Window -> IO ()
actTBOff tb w f pop = do rec {
                          cid <- tb `on` toggled $ io ( widgetDestroy pop >>
                                                       signalDisconnect cid >>
                                                       actTBOn tb w f >> return ())
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

-- | Crea un widget para una expresión. El argumento "initial" indica si es inicial.
-- En ese caso no se crea el botón para ver posibles reescrituras.
-- El argumento "proofIndex" indica el paso de prueba en la cual este widget de expresion
-- se encuentra (a la derecha de tal paso).
createExprWidget :: Bool -> Int -> IState ExprWidget
createExprWidget initial proofIndex = do

    boxExpr <- io $ hBoxNew False 2
    formBox <- io $ hBoxNew False 2
    
    listRw <- showChoicesButton
    choices <- if not initial && listRw
              then do
                exprChoices <- io $ makeButtonWithImage stockIndex
                io $ buttonSetRelief exprChoices ReliefNone >>
                     setToolTip exprChoices "Expresiones posibles"
                return . Just $ exprChoices
              else return Nothing

    bAnnot <- io $ makeButtonBox annotIcon
    bType <- io $ makeButtonBox typeTreeIcon
    bInfo <- io $ imageNewFromStock (imgState Unknown) IconSizeMenu
    io $ setToolTip bInfo (show Unknown)

    io $ do 
        boxPackStart boxExpr formBox PackGrow 2
        if not initial && listRw
        then boxPackStart boxExpr (fromJust choices) PackNatural 2
        else return ()
        boxPackStart boxExpr bAnnot PackNatural 2
        boxPackStart boxExpr bType PackNatural 2
        boxPackStart boxExpr bInfo PackNatural 1 
        widgetSetSizeRequest formBox 400 (-1)
           
    ran <- io $ randomIO
    
    return $ ExprWidget { formBox = formBox
                        , extBox = boxExpr
                        , wExprL = emptyWExprList
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
    flip runEnvBox (expr_w,p,0) $ 
         setupForm (formBox expr_w) Editable "" >>
         writeExprWidget expr >>
         setupOptionInitExprWidget win
               
    return expr_w

setupOptionInitExprWidget :: Window -> IExpr' (ConnectId ToggleButton, ConnectId ToggleButton)
setupOptionInitExprWidget win = ask >>= \env ->
                                lift get >>= \s ->
                                configAnnotTB (loadAnnotation env) 
                                              (saveAnnotation env) s win >>= \cid1 ->
                                configTypeTreeTB win True >>= \ cid2 -> 
                                return (cid1,cid2)
                                
    where
        loadAnnotation :: Env -> IState String
        loadAnnotation env = getProofState >>= \mps ->
                             case mps of
                                Nothing -> return msgAnnotWithoutProof
                                Just _ -> loadInitAnnot
        saveAnnotation :: Env -> String -> IState ()
        saveAnnotation env s = getProofState >>= \mps ->
                               case mps of
                                    Nothing -> return ()
                                    Just _ -> saveInitAnnot s

-- | Carga la anotación de una expresión en base al entorno.
loadInitAnnot :: IState String
loadInitAnnot = getProofAnnots >>= return . unpack . getStartExpr
        
saveInitAnnot :: String -> IState ()
saveInitAnnot s = getProofAnnots >>= updateProofAnnots . updateFirstExpr (pack s)

setupOptionExprWidget :: Window -> IExpr' (ConnectId ToggleButton,ConnectId ToggleButton)
setupOptionExprWidget win  = ask >>= \env ->
                             lift get >>= \s ->
                             configAnnotTB (loadAnnotation env)
                                           (saveAnnotation env)
                                           s win >>= \cid1 ->
                             configTypeTreeTB win False >>= \ cid2 ->
                             return (cid1,cid2)
    where
        loadAnnotation :: Env -> IState String
        loadAnnotation = runReaderT loadAnnot
        saveAnnotation :: Env -> String -> IState ()
        saveAnnotation env = flip runReaderT env . saveAnnot

getAnnot :: ListedAnnots -> Env -> String
getAnnot pfa env = unpack $ getBasicAt (pme env) pfa

-- | Carga la anotaci´on de una expresi´on en base al entorno.
loadAnnot :: IExpr' String
loadAnnot = lift getProofAnnots >>= \p ->
            ask >>= return . getAnnot p

-- | Guarda la anotaci´on para una expresi´on en base al entorno.
saveAnnot :: String -> IExpr' ()
saveAnnot s = lift getProofAnnots >>= \pfa ->
              ask >>= \env -> 
              lift . updateProofAnnots $ updateExprAt (pme env) (pack s) pfa
            

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
                  writeExprWidget expr >>
                  return ()
                        
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
