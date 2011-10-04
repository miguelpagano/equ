{-# Language OverloadedStrings,TypeSynonymInstances,Rank2Types, ExistentialQuantification, ImpredicativeTypes #-}
module Equ.GUI.Utils where

import Equ.Expr
import Equ.PreExpr
import Equ.Theories
import Equ.Types
import Equ.Syntax
import Equ.Parser

import Graphics.UI.Gtk hiding (eventButton, eventSent)
import Graphics.UI.Gtk.Gdk.EventM
import Graphics.UI.Gtk.Glade
import Data.Text
import Data.IORef
import Data.Maybe(fromJust)
import Control.Monad(liftM)
import Control.Monad.IO.Class(liftIO)


type RExpr = IORef Focus
type IState' m a = RExpr -> (Focus -> Focus,Focus -> Focus) -> (Statusbar, ContextId) -> m a
type IState a = IState' IO a

type IRExpr = IState ()

data WExpr w = WExpr { widget :: WidgetClass w => w
                     , getExpr :: PreExpr
                     }

type GoBack = (Focus -> Focus,Focus -> Focus)

holeExpr = preExprHole ""

go :: (Focus -> Maybe Focus) -> Focus -> Focus
go g e = maybe (error $ show e) id $ g e

(.^.) :: GoBack -> GoBack -> GoBack
(f,f') .^. (g,g') = (f . g , g' . f')

(.^) :: (Focus -> Maybe Focus,Focus -> Maybe Focus) -> GoBack -> GoBack
(f,f') .^ (g,g') = (go f . g , g' . go f')


labelStr :: String -> IO Label
labelStr = labelNew . return

showExpr :: RExpr -> (Statusbar,ContextId) -> IO ()
showExpr r (s,c) = readIORef r >>= statusbarPush s c . show . toExpr >> return ()

emptyRef :: IO RExpr
emptyRef = newIORef . toFocus $ holeExpr

updateRef :: PreExpr -> IRExpr
updateRef e r (f,f') sb = (liftM (snd . f) . readIORef) r >>= \p -> 
                          (writeIORef r . f') (e, p) >>
                          showExpr r sb

clearExpr :: BoxClass b => b -> IRExpr
clearExpr b r f sb = removeAllChildren b >>
                     updateRef holeExpr r f sb

-- TODO: manejar errores del parser
setVarFocus :: Entry -> IRExpr
setVarFocus entry r f sb = entryGetText entry >>= \v ->
                           updateRef (varExp v) r f sb
    where varExp :: String -> PreExpr
          varExp v = case parserVar v of 
                       Left err -> error . show $ err
                       Right v' -> Var $ v'

-- TODO: manejar errores del parser.
setExprFocus :: BoxClass b => Entry -> b -> IRExpr
setExprFocus entry box r f sb = entryGetText entry >>= \e ->
                                return (parser e) >>= \expr ->
                                updateRef expr r f sb >>
                                frameExp expr >>= \(WExpr box' _) ->
                                removeAllChildren box >>
                                addToBox box box' >>
                                widgetShowAll box                                


data Boxeable w = forall w . WidgetClass w => Boxeable w

infixr 8 .*.

(.*.) :: (WidgetClass w') => w' -> [Boxeable w] -> [Boxeable w]
w .*. ws = Boxeable w : ws

infix 9 .*:
(.*:) :: (WidgetClass w',WidgetClass w) => w' -> w -> [Boxeable w]
w' .*: w = Boxeable w' : Boxeable w : []

addToBox' :: (BoxClass b) => b -> Boxeable w -> IO ()
addToBox' b (Boxeable w) = boxPackStart b w PackGrow 0

addToBox :: (BoxClass b,WidgetClass w) => b -> w -> IO ()
addToBox b w = boxPackStart b w PackGrow 0


quitAction :: Window -> IO ()
quitAction w = widgetDestroy w

newBox = hBoxNew False 10

frameExp :: PreExpr -> IO (WExpr HBox)
frameExp e@(PrExHole h) = newBox >>= \box ->
                          entryNew >>= \entry ->
                          (entrySetText entry . unpack . tRepr) h >>
                          addToBox box entry >> 
                          return (WExpr box e)
frameExp e@(Var v) = newBox >>= \box ->
                     entryNew >>= \entry ->
                     (entrySetText entry . unpack . tRepr) v >>
                     addToBox box entry >> 
                     return (WExpr box e)
frameExp e@(Con c) = newBox >>= \box ->
                     (labelStr . unpack . tRepr) c >>= \lblConst ->
                     addToBox box lblConst >> 
                     return (WExpr box e)
frameExp e@(UnOp op e') = newBox >>= \box ->
                          frameExp e' >>= \(WExpr box' _) ->
                          (labelStr . unpack . tRepr) op >>= \lblOp ->
                          mapM_ (addToBox' box) (lblOp .*: box') >>
                          return (WExpr box e)
frameExp e@(BinOp op e1 e2) = newBox >>= \box ->
                              frameExp e1 >>= \(WExpr box1 _) ->
                              frameExp e2 >>= \(WExpr box2 _) ->
                              (labelStr . unpack . tRepr) op >>= \lblOp ->
                              mapM_ (addToBox' box) ( box1 .*. lblOp .*: box2) >>
                              return (WExpr box e)
frameExp e@(Quant q v e1 e2) = newBox >>= \box ->
                               frameExp (Var v) >>= \(WExpr vbox _) ->
                               frameExp e1 >>= \(WExpr box1 _) ->
                               frameExp e2 >>= \(WExpr box2 _) ->
                               labelStr (quantInit ++ (unpack $ tRepr q)) >>= \lblQnt ->
                               labelStr ":" >>= \lblRng ->
                               labelStr ":" >>= \lblTrm -> 
                               labelStr quantEnd >>= \lblEnd ->
                               mapM_ (addToBox' box) (   lblQnt
                                                     .*. vbox
                                                     .*. lblRng
                                                     .*. box1
                                                     .*. lblTrm
                                                     .*. box2
                                                     .*: lblEnd
                                                      ) >>

                               return (WExpr box e)
frameExp e@(Paren e') = newBox >>= \box ->
                        frameExp e' >>= \(WExpr box1 _) ->
                        labelStr "[" >>= \lblOpen ->
                        labelStr "]" >>= \lblClose -> 
                        mapM_ (addToBox' box) (lblOpen .*. box1 .*: lblClose) >>
                        return (WExpr box e)
                        



frameQuant :: (BoxClass b, WidgetClass w) => Variable -> WExpr w -> WExpr w -> Quantifier -> b -> IRExpr
frameQuant v rng trm q box r f sb = do 
    let expr = Quant q v (getExpr rng) (getExpr trm)
    updateRef expr r f sb
    lblQnt  <- labelStr $ quantInit ++ (unpack $ tRepr q)
    entryVar <- entryNew    
    setupLabel box lblQnt r f sb

    set entryVar [ entryEditable := True ]
    
    onEntryActivate entryVar (setVarQuant r entryVar sb)

    widgetSetSizeRequest entryVar 10 (-1)

    lblRng <- labelStr ":"
    lblTrm <- labelStr ":"
    lblEnd <- labelStr quantEnd

    mapM_ (addToBox' box) (  lblQnt
                         .*. entryVar 
                         .*. lblRng
                         .*. widget rng
                         .*. lblTrm
                         .*. widget trm
                         .*: lblEnd
                         )

    widgetShowAll box

frameUnOp :: (BoxClass b,WidgetClass w) => Operator -> WExpr w -> b -> IRExpr
frameUnOp op expr box r f sb = do
    lblOp <- labelStr . unpack $ tRepr op
    setupLabel box lblOp r f sb

    updateRef (UnOp op (getExpr expr)) r f sb

    addToBox box lblOp
    addToBox box (widget expr)

    widgetShowAll box


frameBinOp :: (BoxClass b,WidgetClass w) => Operator -> WExpr w -> WExpr w -> b -> IRExpr
frameBinOp op expr expr' box r f sb = do
    lblOp <- labelStr . unpack $ tRepr op
    updateRef (BinOp op (getExpr expr) (getExpr expr')) r f sb

    addToBox box (widget expr)
    setupLabel box lblOp r f sb
    addToBox box (widget expr')
    

    widgetShowAll box


loadItems :: (BoxClass b) => Menu -> b -> IRExpr
loadItems menu box r f sb = do
    appendItems quantifiersList
    appendItems operatorsList
    appendItems constantsList
    appendItemVariable 
    appendItemPreExpr
    
    where appendItems :: (Syntactic s,ExpWriter s) => [s] -> IO ()
          appendItems [] = return ()
          appendItems (x:xs) = do
              item <- menuItemNewWithLabel $ unpack $ tRepr x
              onActivateLeaf item $ writeExp x box r f sb
              menuShellAppend menu item
              appendItems xs
              
          appendItemVariable = do
              item <- menuItemNewWithLabel "Variable"
              onActivateLeaf item (writeVarExp box r f sb)
              menuShellAppend menu item
              
          appendItemPreExpr = do
              item <- menuItemNewWithLabel "Expresión"
              onActivateLeaf item (writeExpr box r f sb)
              menuShellAppend menu item
              


setVarQuant :: RExpr -> Entry -> (Statusbar, ContextId) -> IO ()
setVarQuant r entry sb = do v <- entryGetText entry
                            (e,p) <- readIORef r
                            case e of
                              (Quant q _ rng trm) -> writeIORef r (exp q v rng trm ,p)
                              _ -> return ()
                            showExpr r sb
    where exp q v r t  = Quant q (var (pack v) TyUnknown) r t



writeOperator :: (BoxClass b) => Operator -> b -> IRExpr
writeOperator o box r f sb = 
    case opNotationTy o of
        NPrefix -> do
            boxExpr <- newBox
            mkButtonSubExpr boxExpr r ((goDown,goUp) .^ f) sb
            frameUnOp o (WExpr boxExpr holeExpr) box r f sb

        NPostfix -> do
            boxExpr <- newBox
            mkButtonSubExpr boxExpr r ((goDown,goUp) .^ f) sb
            frameUnOp o (WExpr boxExpr holeExpr) box r f sb

             
        NInfix -> do
            boxExpr <- newBox
            mkButtonSubExpr boxExpr r ((goDown, goUp) .^ f) sb
            boxExpr' <- newBox
            mkButtonSubExpr boxExpr' r ((goDownR, goUp) .^ f) sb

            frameBinOp o (WExpr boxExpr holeExpr) 
                         (WExpr boxExpr' holeExpr) 
                         box r f sb



writeQuantifier ::  (BoxClass b) => Quantifier -> b -> IRExpr
writeQuantifier q box r f sb = do

    boxRng <- newBox
    boxTrm <- newBox
    
    mkButtonSubExpr boxRng r ((goDown, goUp) .^ f) sb
    mkButtonSubExpr boxTrm r ((goDownR,goUp) .^ f) sb

    frameQuant (var "" TyUnknown) 
               (WExpr boxRng (preExprHole ""))
               (WExpr boxTrm (preExprHole "")) 
               q box r f sb
    return ()
    


writeConstant :: (BoxClass b) => Constant -> b -> IRExpr
writeConstant c box r f sb = do
    updateRef (Con c) r f sb
    label <- labelStr . unpack $ tRepr c
    setupLabel box label r f sb
    addToBox box label
    widgetShowAll box


writeVarExp :: (BoxClass b) => b -> IRExpr
writeVarExp box r f sb = entryNew >>= \entry ->
                         onEntryActivate entry (setVarFocus entry r f sb) >>                                         
                         widgetSetSizeRequest entry 10 (-1) >>
                         removeAllChildren box >>
                         addToBox box entry >>
                         widgetGrabFocus entry >>
                         widgetShowAll box
    


writeVarExpName :: (BoxClass b) => Variable -> b -> IRExpr
writeVarExpName v box r f sb = entryNew >>= \entry -> 
                               (entrySetText entry . unpack . tRepr) v >>
                               onEntryActivate entry (setVarFocus entry r f sb) >>
                               widgetSetSizeRequest entry 10 (-1) >>
                               removeAllChildren box >> 
                               addToBox box entry >> 
                               widgetGrabFocus entry >> 
                               widgetShowAll box
    

writeExpr :: (BoxClass b) => b -> IRExpr
writeExpr box r f sb =  entryNew >>= \entry -> 
                        onEntryActivate entry (setExprFocus entry box r f sb) >>
                        widgetSetSizeRequest entry 10 (-1) >>
                        removeAllChildren box >>
                        addToBox box entry >>
                        widgetGrabFocus entry >>
                        widgetShowAll box
    
removeAllChildren :: (BoxClass b) => b -> IO ()
removeAllChildren b = containerForeach b (containerRemove b)

mkButtonSubExpr :: (BoxClass b) => b -> IRExpr
mkButtonSubExpr box r f sb = do
    butExpr <- buttonNewWithLabel "Expresión"
    addToBox box butExpr
    menuSymbols <- menuNew
    loadItems menuSymbols box r f sb
    onPressed butExpr $ menuPopup menuSymbols Nothing
    widgetShowAll menuSymbols


setupLabel :: (BoxClass b, WidgetClass w) => b -> w -> IState (EventBox,w)
setupLabel b w r f sb = do
    eb <- eventBoxNew
    boxPackStart b eb PackGrow 0
    set eb [ containerChild := w ]
    st <- widgetGetStyle b
    bg <- styleGetBackground st (toEnum 0)
    eb `on` buttonPressEvent $ tryEvent $ (removeExpr b eb r f sb)
    eb `on` enterNotifyEvent $ tryEvent $ highlightBox b eb
    eb `on` leaveNotifyEvent $ tryEvent $ unlightBox b eb bg
    return (eb, w)

--removeExpr :: BoxClass b => b -> EventBox -> EventM IO ()
removeExpr b eb r f sb = do RightButton <- eventButton
                            liftIO $ updateRef (preExprHole "") r f sb 
                            liftIO $ removeAllChildren b 
                            liftIO $ mkButtonSubExpr b r f sb
                            liftIO $ widgetShowAll b


highlightBox b eb = liftIO $ containerForeach b highlight
unlightBox b eb bg = liftIO $ containerForeach b (unlight bg)

highlight :: WidgetClass w => w -> IO ()
highlight w = widgetModifyBg w (toEnum 0) (Color 32000 32000 32000)

unlight :: WidgetClass w => Color -> w -> IO ()
unlight bg w = widgetModifyBg w (toEnum 0) bg

class ExpWriter s where
    writeExp :: (BoxClass b) => s -> b -> IRExpr

instance ExpWriter Quantifier where
    writeExp s cont r f sb = removeAllChildren cont >>
                             writeQuantifier s cont r f sb
    
instance ExpWriter Operator where
    writeExp s cont r f sb = removeAllChildren cont >>
                             writeOperator s cont r f sb

instance ExpWriter Constant where
    writeExp s cont r f sb = removeAllChildren cont >>
                             writeConstant s cont r f sb


