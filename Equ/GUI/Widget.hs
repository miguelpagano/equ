{-# Language OverloadedStrings,TypeSynonymInstances,Rank2Types, ExistentialQuantification #-}
module Equ.GUI.Widget where

import Equ.GUI.Types
import Equ.GUI.Utils

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



labelStr :: String -> IO Label
labelStr = labelNew . return


clearExpr :: HBox -> IRExpr
clearExpr b r f sb = removeAllChildren b >>
                     updateExpr holeExpr r f sb

-- TODO: manejar errores del parser
setVarFocus :: Entry -> IRExpr
setVarFocus entry r f sb = entryGetText entry >>= \v ->
                           updateExpr (varExp v) r f sb
    where varExp :: String -> PreExpr
          varExp v = case parserVar v of 
                       Left err -> error . show $ err
                       Right v' -> Var $ v'

-- TODO: manejar errores del parser.
setExprFocus :: Entry -> HBox -> IRExpr
setExprFocus entry box r f sb = entryGetText entry >>= \e ->
                                return (parser e) >>= \expr ->
                                updateExpr expr r f sb >>
                                frameExp expr >>= \(WExpr box' _) ->
                                removeAllChildren box >>
                                addToBox box box' >>
                                widgetShowAll box                                



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
                        



frameQuant :: (WidgetClass w) => Variable -> WExpr w -> WExpr w -> Quantifier -> HBox -> IRExpr
frameQuant v rng trm q box r f sb = do 
    let expr = Quant q v (getExpr rng) (getExpr trm)
    updateExpr expr r f sb
    lblQnt  <- labelStr $ quantInit ++ (unpack $ tRepr q)
    entryVar <- entryNew    
    setupLabel box lblQnt r f sb

    set entryVar [ entryEditable := True ]
    
    onEntryActivate entryVar (entryGetText entryVar >>= \v -> updateQVar v r (id,id) sb)

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

frameUnOp :: (WidgetClass w) => Operator -> WExpr w -> HBox -> IRExpr
frameUnOp op expr box r f sb = do
    lblOp <- labelStr . unpack $ tRepr op
    setupLabel box lblOp r f sb

    updateExpr (UnOp op (getExpr expr)) r f sb

    addToBox box lblOp
    addToBox box (widget expr)

    widgetShowAll box


frameBinOp :: (WidgetClass w) => Operator -> WExpr w -> WExpr w -> HBox -> IRExpr
frameBinOp op expr expr' box r f sb = do
    lblOp <- labelStr . unpack $ tRepr op
    updateExpr (BinOp op (getExpr expr) (getExpr expr')) r f sb

    addToBox box (widget expr)
    setupLabel box lblOp r f sb
    addToBox box (widget expr')
    

    widgetShowAll box


writeOperator :: Operator -> HBox -> IRExpr
writeOperator o box r f sb = 
    case opNotationTy o of
        NPrefix -> do
            boxExpr <- newBox
            setupForm boxExpr r ((goDown,goUp) .^ f) sb
            frameUnOp o (WExpr boxExpr holeExpr) box r f sb

        NPostfix -> do
            boxExpr <- newBox
            setupForm boxExpr r ((goDown,goUp) .^ f) sb
            frameUnOp o (WExpr boxExpr holeExpr) box r f sb

             
        NInfix -> do
            boxExpr <- newBox
            setupForm boxExpr r ((goDown, goUp) .^ f) sb
            boxExpr' <- newBox
            setupForm boxExpr' r ((goDownR, goUp) .^ f) sb

            frameBinOp o (WExpr boxExpr holeExpr) 
                         (WExpr boxExpr' holeExpr) 
                         box r f sb



writeQuantifier :: Quantifier -> HBox -> IRExpr
writeQuantifier q box r f sb = do

    boxRng <- newBox
    boxTrm <- newBox
    
    setupForm boxRng r ((goDown, goUp) .^ f) sb
    setupForm boxTrm r ((goDownR,goUp) .^ f) sb

    frameQuant (var "" TyUnknown) 
               (WExpr boxRng (preExprHole ""))
               (WExpr boxTrm (preExprHole "")) 
               q box r f sb
    return ()
    


writeConstant :: Constant -> HBox -> IRExpr
writeConstant c box r f sb = do
    updateExpr (Con c) r f sb
    label <- labelStr . unpack $ tRepr c
    setupLabel box label r f sb
    addToBox box label
    widgetShowAll box


writeVarExp :: HBox -> IRExpr
writeVarExp box r f sb = entryNew >>= \entry ->
                         onEntryActivate entry (setVarFocus entry r f sb) >>                                         
                         widgetSetSizeRequest entry 10 (-1) >>
                         removeAllChildren box >>
                         addToBox box entry >>
                         widgetGrabFocus entry >>
                         widgetShowAll box
    


writeVarExpName :: Variable -> HBox -> IRExpr
writeVarExpName v box r f sb = entryNew >>= \entry -> 
                               (entrySetText entry . unpack . tRepr) v >>
                               onEntryActivate entry (setVarFocus entry r f sb) >>
                               widgetSetSizeRequest entry 10 (-1) >>
                               removeAllChildren box >> 
                               addToBox box entry >> 
                               widgetGrabFocus entry >> 
                               widgetShowAll box
    

writeExpr :: HBox -> IRExpr
writeExpr box r f sb =  entryNew >>= \entry -> 
                        onEntryActivate entry (setExprFocus entry box r f sb) >>
                        widgetSetSizeRequest entry 10 (-1) >>
                        removeAllChildren box >>
                        addToBox box entry >>
                        widgetGrabFocus entry >>
                        widgetShowAll box
    
removeAllChildren :: HBox -> IO ()
removeAllChildren b = containerForeach b (containerRemove b)

setupForm ::  HBox -> IRExpr
setupForm b r f sb = labelStr "?" >>= \lblForm -> 
                     eventBoxNew >>= \eb ->
                     addToBox b eb >>
                     set eb [ containerChild := lblForm ] >>
                     setupEvents b eb r f sb

newFocusToSym l r = do LeftButton <- eventButton 
                       liftIO $ updateFrmCtrl l r
                       sym <- liftIO $ getSymCtrl r 
                       liftIO $ widgetGrabFocus sym

                            
setupEvents b eb r f sb = do st <- widgetGetStyle b
                             bg <- styleGetBackground st (toEnum 0)
                             eb `on` buttonPressEvent $ tryEvent $ newFocusToSym b r
                             eb `on` buttonPressEvent $ tryEvent $ removeExpr b r f sb
                             eb `on` enterNotifyEvent $ tryEvent $ highlightBox b
                             eb `on` leaveNotifyEvent $ tryEvent $ unlightBox b bg
                             return ()
--    where events = [ ButtonPressMask, LeaveNotifyMask, FocusChangeMask ]

setupLabel :: HBox -> Label -> IRExpr
setupLabel b w r f sb = eventBoxNew >>= \eb ->
                        addToBox b eb >>
                        set eb [ containerChild := w ] >>
                        setupEvents b eb r f sb

removeExpr b r f sb = do RightButton <- eventButton
                         liftIO $ updateExpr holeExpr r f sb 
                         liftIO $ removeAllChildren b 
                         liftIO $ setupForm b r f sb
                         liftIO $ widgetShowAll b


highlightBox b = liftIO $ containerForeach b highlight
unlightBox b bg = liftIO $ containerForeach b (unlight bg)

highlight :: WidgetClass w => w -> IO ()
highlight w = widgetModifyBg w (toEnum 0) (Color 32000 0 0)

unlight :: WidgetClass w => Color -> w -> IO ()
unlight bg w = widgetModifyBg w (toEnum 0) bg

class ExpWriter s where
    writeExp :: s -> HBox -> IRExpr

instance ExpWriter Quantifier where
    writeExp s cont r f sb = removeAllChildren cont >>
                             writeQuantifier s cont r f sb
    
instance ExpWriter Operator where
    writeExp s cont r f sb = removeAllChildren cont >>
                             writeOperator s cont r f sb

instance ExpWriter Constant where
    writeExp s cont r f sb = removeAllChildren cont >>
                             writeConstant s cont r f sb


