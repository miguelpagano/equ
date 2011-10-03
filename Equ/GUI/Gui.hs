{-# Language OverloadedStrings #-}
-- | Interfaz gráfica de Equ.
module Equ.GUI.Gui where

import Equ.Expr
import Equ.PreExpr
import Equ.Theories
import Equ.Types
import Equ.Syntax
import Equ.Parser

import Graphics.UI.Gtk
import Graphics.UI.Gtk.Gdk.Events
import Graphics.UI.Gtk.Glade
import Data.Text
import Data.IORef
import Data.Maybe(fromJust)
import Control.Monad(liftM)

type RExpr = IORef Focus
type IState a = RExpr -> (Focus -> Focus,Focus -> Focus) -> (Statusbar, ContextId) -> IO a

type IRExpr = IState ()

go :: (Focus -> Maybe Focus) -> Focus -> Focus
go g e= maybe (error $ show e) id $ g e

showExpr :: RExpr -> (Statusbar,ContextId) -> IO ()
showExpr r (s,c) = readIORef r >>= statusbarPush s c . show . toExpr >> return ()

emptyRef :: IO RExpr
emptyRef = newIORef . toFocus $ preExprHole ""

updateRef :: PreExpr -> IRExpr
updateRef e r (f,f') sb = do (_,p) <- liftM f . readIORef $ r                     
                             writeIORef r . f' $ (e, p)
                             showExpr r sb

class Syntactic s => ExpWriter s where
    writeExp :: (BoxClass b) => s -> b -> IRExpr
    writeExp s box r f sb = undefined
        
       -- entrySetText entry (unpack $ tRepr s)

instance ExpWriter Quantifier where
    writeExp s container r f sb = do
        removeAllChilds container
        writeQuantifier s container r f sb
        
        
        --entrySetText entry ("〈" ++ (unpack $ tRepr s) ++ "   : (  ) : (  ) 〉")
    --writeExp s entry = entrySetText entry ("〈" ++ (unpack $ tRepr s) ++ "   : (  ) : (  ) 〉")
    
instance ExpWriter Operator where
    writeExp s container r f sb = do
        removeAllChilds container
        writeOperator s container r f sb
    {-writeExp s entry = case opNotationTy s of
                            NPrefix  -> entrySetText entry $ (unpack $ tRepr s) ++ "(  )"
                            NInfix   -> entrySetText entry $ "(  ) " ++(unpack $ tRepr s) ++ " (  )"
                            NPostfix -> entrySetText entry $ "(  ) " ++(unpack $ tRepr s)
                            -}
instance ExpWriter Constant where
    writeExp s container r f sb = do
        removeAllChilds container
        writeConstant s container r f sb

getMenuButton :: GladeXML -> String -> IO MenuItem
getMenuButton w = xmlGetWidget w castToMenuItem 

quitAction :: Window -> IO ()
quitAction w = widgetDestroy w

main :: IO ()
main = do
    initGUI
    Just xml <- xmlNew "Equ/GUI/interfaz1.glade"
    exprRef <- emptyRef

    -- get widgets
    window <- xmlGetWidget xml castToWindow "window1"
    box_formula <- xmlGetWidget xml castToHBox "box_formula"
    button_expr <- xmlGetWidget xml castToButton "button_expr"
    applyButton <- xmlGetWidget xml castToButton "applyButton"
    quitButton <- getMenuButton xml "QuitButton"

    statusBar <- xmlGetWidget xml castToStatusbar "statusBar"
    ctxExpr <- statusbarGetContextId statusBar "Expr"


    menu_symbols <- menuNew
    loadItems menu_symbols box_formula exprRef (id,id) (statusBar,ctxExpr)

    -- signals
    onPressed button_expr $ menuPopup menu_symbols Nothing
    onPressed applyButton $ menuPopup menu_symbols Nothing
    onActivateLeaf quitButton $ quitAction window
    onDestroy window mainQuit
    
    widgetShowAll menu_symbols
    widgetShowAll window
    mainGUI


loadItems :: (BoxClass b) => Menu -> b -> IRExpr
loadItems menu box r f sb = do
    appendItems quantifiersList
    appendItems operatorsList
    appendItems constantsList
    
    where appendItems :: ExpWriter s => [s] -> IO ()
          appendItems [] = return ()
          appendItems (x:xs) = do
              item <- menuItemNewWithLabel $ unpack $ tRepr x
              onActivateLeaf item $ writeExp x box r f sb
              menuShellAppend menu item
              appendItems xs

setValueQuant :: RExpr -> Entry -> (Statusbar, ContextId) -> IO ()
setValueQuant r entry sb = do v <- entryGetText entry
                              (e,p) <- readIORef r
                              case e of
                                (Quant q _ rng trm) -> writeIORef r (exp q v rng trm ,p)
                                _ -> return ()
                              showExpr r sb
    where exp q v r t  = Quant q (var (pack v) TyUnknown) r t

writeQuantifier ::  (BoxClass b) => Quantifier -> b -> IRExpr
writeQuantifier q box r f sb = do
    updateRef (Quant q (var "" TyUnknown) (preExprHole "") (preExprHole "")) r f sb

    label_init  <- labelNew (Just (quantInit ++ (unpack $ tRepr q)))
    entryVar    <- entryNew

    set entryVar [ entryEditable := True ]
    
    onEntryActivate entryVar (setValueQuant r entryVar sb)

    label_dots1 <- labelNew (Just ":")
    box_sub_expr1 <- hBoxNew False 10
    label_dots2 <- labelNew (Just ":")
    box_sub_expr2 <- hBoxNew False 10
    label_end   <- labelNew (Just quantEnd)
    
    createButtonSubExpr box_sub_expr1 r (go goDown, go goUp) sb
    createButtonSubExpr box_sub_expr2 r (go goDownR, go goUp) sb
    
    boxPackStart box label_init PackGrow 0
    boxPackStart box entryVar PackGrow 0
    boxPackStart box label_dots1 PackGrow 0
    boxPackStart box box_sub_expr1 PackGrow 0
    boxPackStart box label_dots2 PackGrow 0
    boxPackStart box box_sub_expr2 PackGrow 0
    boxPackStart box label_end PackGrow 0
    
    widgetShowAll box
    
    -- DUDA: Lo siguiente no funciona porque no se puede definir una lista
    -- de tipos distintos.
    -- packWidgets box [label_init,entry_var,label_dots1,box_sub_expr1,
    --                label_dots2,box_sub_expr2,label_end] PackGrow 0

writeOperator ::  (BoxClass b) => Operator -> b -> IRExpr
writeOperator o box r f sb = 
    case opNotationTy o of
        NPrefix -> do
            updateRef (UnOp o (preExprHole "")) r f sb
            box_sub_expr <- hBoxNew False 10
            createButtonSubExpr box_sub_expr r (go goDown,go goUp) sb
            label <- labelNew (Just (unpack $ tRepr o))
            boxPackStart box label PackGrow 0
            boxPackStart box box_sub_expr PackGrow 0
            widgetShowAll box
             
        NInfix -> do
            updateRef (BinOp o (preExprHole "") (preExprHole "")) r f sb
            box_sub_expr1 <- hBoxNew False 10
            createButtonSubExpr box_sub_expr1 r (go goDown, go goUp) sb
            box_sub_expr2 <- hBoxNew False 10
            createButtonSubExpr box_sub_expr2 r (go goDownR, go goUp) sb
            label <- labelNew (Just (unpack $ tRepr o))
            boxPackStart box box_sub_expr1 PackGrow 0
            boxPackStart box label PackGrow 0
            boxPackStart box box_sub_expr2 PackGrow 0
            widgetShowAll box
            
        NPostfix -> do
            updateRef (UnOp o (preExprHole "")) r f sb
            box_sub_expr <- hBoxNew False 10
            createButtonSubExpr box_sub_expr r (go goDown, go goUp) sb
            label <- labelNew (Just (unpack $ tRepr o))
            boxPackStart box box_sub_expr PackGrow 0
            boxPackStart box label PackGrow 0
            widgetShowAll box


writeConstant :: (BoxClass b) => Constant -> b -> IRExpr
writeConstant c box r f sb = do
    updateRef (Con c) r f sb
    label <- labelNew (Just (unpack $ tRepr c))
    boxPackStart box label PackGrow 0
    widgetShowAll box

-- packWidgets ::(BoxClass box, WidgetClass child) =>
--               box -> [child] -> Packing -> Int -> IO () 
-- packWidgets b [] p i = return ()
-- packWidgets b (x:xs) p i = do
--     boxPackStart b x p i
--     packWidgets b xs p i

removeAllChilds :: (BoxClass b) => b -> IO ()
removeAllChilds b = containerForeach b (removeChild b)
    where removeChild :: (BoxClass b,WidgetClass child) => b -> child -> IO ()
          removeChild b c = containerRemove b c


createButtonSubExpr :: (BoxClass b) => b -> IRExpr
createButtonSubExpr box r f sb = do
    button_sub_expr <- buttonNewWithLabel "Expresión"
    boxPackStart box button_sub_expr PackGrow 0
    menu_symbols <- menuNew
    loadItems menu_symbols box r f sb
    onPressed button_sub_expr $ menuPopup menu_symbols Nothing
    widgetShowAll menu_symbols

