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
                     setupForm b r f sb >> 
                     widgetShowAll b


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
                                frameExp expr box r f sb >>= \(WExpr box' _) ->
                                removeAllChildren box >>
                                addToBox box box' >>
                                widgetShowAll box                                



addToBox' :: (BoxClass b) => b -> Boxeable w -> IO ()
addToBox' b (Boxeable w) = boxPackStart b w PackGrow 2

addToBox :: (BoxClass b,WidgetClass w) => b -> w -> IO ()
addToBox b w = boxPackStart b w PackGrow 2


quitAction :: Window -> IO ()
quitAction w = widgetDestroy w

newBox = hBoxNew False 10

frameExp :: PreExpr -> HBox -> IState (WExpr HBox)
frameExp e@(PrExHole h) b r f sb = newBox >>= \box ->
                                   entryNew >>= \entry ->
                                   (entrySetText entry . unpack . tRepr) h >>
                                   setupFormE box entry r f sb >> 
                                   return (WExpr box e)
frameExp e@(Var v) b r f sb = newBox >>= \box ->
                              entryNew >>= \entry ->
                              (entrySetText entry . unpack . tRepr) v >>
                              setupFormE box entry r f sb >> 
                              return (WExpr box e)
frameExp e@(Con c) b r f sb = newBox >>= \box ->
                              (labelStr . unpack . tRepr) c >>= \lblConst ->
                              setupFormE box lblConst r f sb >> 
                              return (WExpr box e)
frameExp e@(UnOp op e') b r f sb = newBox >>= \box -> 
                                   frameExp e' box r ((goDown,goUp) .^ f) sb >>= \(WExpr box' _) ->
                                   (labelStr . unpack . tRepr) op >>= \lblOp ->
                                   setupLabel box lblOp r f sb >>
                                   setupFormE box box' r f sb >>
                                   labelStr " " >>= \lblEnd ->
                                   setupLabel box lblEnd r f sb >>
                                   return (WExpr box e)
frameExp e@(BinOp op e1 e2) b r f sb = newBox >>= \box ->
                                       frameExp e1 box r ((goDown,goUp) .^ f) sb >>= \(WExpr box1 _) ->
                                       frameExp e2 box r ((goDownR,goUp) .^ f) sb >>= \(WExpr box2 _) ->
                                       (labelStr . unpack . tRepr) op >>= \lblOp ->
                                       labelStr  " " >>= \lblEnd ->
                                       setupLabel box lblEnd r f sb >>                                 
                                       setupFormE box box1 r f sb >>
                                       setupLabel box lblOp r f sb >>
                                       setupFormE box box2 r f sb >>
                                       setupLabel box lblEnd r f sb >>
                                       mapM_ (\x -> setupFormE' box x r f sb) ( box1 .*. lblOp .*: box2) >>
                                       return (WExpr box e)
frameExp e@(App e1 e2) b r f sb = newBox >>= \box ->
                                  frameExp e1 box r ((goDown,goUp) .^ f) sb >>= \(WExpr box1 _) ->
                                  frameExp e2 box r ((goDownR,goUp) .^ f) sb >>= \(WExpr box2 _) ->
                                  labelStr  " " >>= \lblEnd ->
                                  setupLabel box lblEnd r f sb >>                                 
                                  setupFormE box box1 r f sb >>
                                  setupLabel box lblEnd r f sb >>
                                  setupFormE box box2 r f sb >>
                                  setupLabel box lblEnd r f sb >>
                                  return (WExpr box e)
frameExp e@(Quant q v e1 e2) b r f sb = newBox >>= \box ->
                                        frameExp (Var v) box r f sb >>= \(WExpr vbox _) ->
                                        frameExp e1 box r ((goDown,goUp) .^ f) sb >>= \(WExpr box1 _) ->
                                        frameExp e2 box r ((goDownR,goUp) .^ f) sb >>= \(WExpr box2 _) ->
                                        labelStr (quantInit ++ (unpack $ tRepr q)) >>= \lblQnt ->
                                        labelStr ":" >>= \lblRng ->
                                        labelStr ":" >>= \lblTrm -> 
                                        labelStr quantEnd >>= \lblEnd ->
                                        setupLabel box lblQnt r f sb >>
                                        addToBox box vbox  >>
                                        setupLabel box lblRng r f sb >>
                                        addToBox box box1 >>
                                        setupLabel box lblTrm r f sb >>
                                        addToBox box box2 >>
                                        setupLabel box lblEnd r f sb >>

                                        return (WExpr box e)

frameExp e@(Paren e') b r f sb = newBox >>= \box ->
                                 frameExp e' box r ((goDown,goUp) .^ f) sb >>= \(WExpr box1 _) ->
                                 labelStr "[" >>= \lblOpen ->
                                 labelStr "]" >>= \lblClose -> 
                                 setupLabel box lblOpen r f sb >>
                                 setupFormE box box1 r f sb >>
                                 setupLabel box  lblClose r f sb >>
                                 return (WExpr box e)
                        



frameQuant :: (WidgetClass w) => Variable -> WExpr w -> WExpr w -> Quantifier -> HBox -> IRExpr
frameQuant v rng trm q box r f sb = do 
    let expr = Quant q v (getExpr rng) (getExpr trm)
    updateExpr expr r f sb
    lblQnt  <- labelStr $ quantInit ++ (unpack $ tRepr q)
    entryVar <- entryNew    

    set entryVar [ entryEditable := True ]
    
    onEntryActivate entryVar (entryGetText entryVar >>= \v -> updateQVar v r (id,id) sb)

    widgetSetSizeRequest entryVar 10 (-1)

    lblRng <- labelStr ":"
    lblTrm <- labelStr ":"

    setupLabel box lblQnt r f sb
    addToBox box entryVar 
    setupLabel box lblRng r f sb
    addToBox box $ widget rng
    setupLabel box lblTrm r f sb
    addToBox box $ widget trm
    lblEnd <- labelStr quantEnd
    setupLabel box lblEnd r f sb

    widgetShowAll box

frameUnOp :: (WidgetClass w) => Operator -> WExpr w -> HBox -> IRExpr
frameUnOp op expr box r f sb = do
    lblOp <- labelStr . unpack $ tRepr op
    setupLabel box lblOp r f sb

    updateExpr (UnOp op (getExpr expr)) r f sb

    addToBox box (widget expr)
    lblEnd <- labelStr " "
    setupLabel box lblEnd r f sb
    widgetShowAll box


frameBinOp :: (WidgetClass w) => Operator -> WExpr w -> WExpr w -> HBox -> IRExpr
frameBinOp op expr expr' box r f sb = do
    lblOp <- labelStr . unpack $ tRepr op
    updateExpr (BinOp op (getExpr expr) (getExpr expr')) r f sb

    lblSt <- labelStr " "
    setupLabel box lblSt r f sb

    addToBox box (widget expr)
    setupLabel box lblOp r f sb
    addToBox box (widget expr')
    lblEnd <- labelStr " "
    setupLabel box lblEnd r f sb
    
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

removeExpr b r f sb = do RightButton <- eventButton
                         liftIO $ updateExpr holeExpr r f sb 
                         liftIO $ removeAllChildren b 
                         liftIO $ setupForm b r f sb
                         liftIO $ widgetShowAll b

setupForm ::  HBox -> IRExpr
setupForm b r f sb = labelStr "?" >>= \lblForm -> 
                     eventBoxNew >>= \eb ->
                     addToBox b eb >>
                     set eb [ containerChild := lblForm ] >>
                     setupEvents b eb r f sb

setupFormE :: WidgetClass w => HBox -> w -> IRExpr
setupFormE b c r f sb = eventBoxNew >>= \eb ->
                        addToBox b eb >>
                        set eb [ containerChild := c ] >>
                        setupEvents b eb r f sb

setupFormE' :: HBox -> Boxeable w -> IRExpr
setupFormE' b (Boxeable c) r f sb = eventBoxNew >>= \eb ->
                                    setupFormE b eb r f sb >>
                                    set eb [ containerChild := c ] >>
                                    setupEvents b eb r f sb


newFocusToSym l r f = do LeftButton <- eventButton 
                         liftIO $ updateFrmCtrl l r
                         liftIO $ updatePath f r
                         sym <- liftIO $ getSymCtrl r
                         liftIO $ widgetGrabFocus sym

                            
setupEvents b eb r f sb = do st <- widgetGetStyle b
                             bg <- styleGetBackground st (toEnum 0)
                             eb `on` buttonPressEvent $ tryEvent $ newFocusToSym b r f
                             eb `on` buttonPressEvent $ tryEvent $ removeExpr b r f sb
                             eb `on` enterNotifyEvent $ tryEvent $ highlightBox b
                             eb `on` leaveNotifyEvent $ tryEvent $ unlightBox b bg
                             return ()

setupLabel :: HBox -> Label -> IRExpr
setupLabel b w r f sb = eventBoxNew >>= \eb ->
                        addToBox b eb >>
                        set eb [ containerChild := w ] >>
                        setupEvents b eb r f sb


highlightBox b = do liftIO $ containerForeach b highlight
unlightBox b bg = do liftIO $ containerForeach b (unlight bg) 


highlight :: WidgetClass w => w -> IO ()
highlight w = widgetModifyBg w (toEnum 0) (Color 32000 3000 0)

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



