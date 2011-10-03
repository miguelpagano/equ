import Graphics.UI.Gtk
import Graphics.UI.Gtk.Glade
import Data.Text
import Equ.Theories
import Equ.Syntax
import Equ.Parser

class Syntactic s => ExpWriter s where
    writeExp :: (BoxClass b) => s -> b -> IO ()
    writeExp s box = undefined
        
       -- entrySetText entry (unpack $ tRepr s)

instance ExpWriter Quantifier where
    writeExp s container = do
        removeAllChilds container
        writeQuantifier s container
        
        
        --entrySetText entry ("〈" ++ (unpack $ tRepr s) ++ "   : (  ) : (  ) 〉")
    --writeExp s entry = entrySetText entry ("〈" ++ (unpack $ tRepr s) ++ "   : (  ) : (  ) 〉")
    
instance ExpWriter Operator where
    writeExp s container = do
        removeAllChilds container
        writeOperator s container
    {-writeExp s entry = case opNotationTy s of
                            NPrefix  -> entrySetText entry $ (unpack $ tRepr s) ++ "(  )"
                            NInfix   -> entrySetText entry $ "(  ) " ++(unpack $ tRepr s) ++ " (  )"
                            NPostfix -> entrySetText entry $ "(  ) " ++(unpack $ tRepr s)
                            -}
instance ExpWriter Constant where
    writeExp s container = do
        removeAllChilds container
        writeConstant s container

main = do
    initGUI
    Just xml <- xmlNew "Equ/GUI/interfaz1.glade"
    
    -- get widgets
    window <- xmlGetWidget xml castToWindow "window1"
    box_formula <- xmlGetWidget xml castToHBox "box_formula"
    button_expr <- xmlGetWidget xml castToButton "button_expr"
    
    menu_symbols <- menuNew
    loadItems menu_symbols box_formula

    -- signals
    onPressed button_expr (menuPopup menu_symbols Nothing)
    onDestroy window mainQuit
    
    widgetShowAll menu_symbols
    widgetShowAll window
    mainGUI

loadItems :: (BoxClass b) => Menu -> b -> IO ()
loadItems menu box = do
    appendItems quantifiersList
    appendItems operatorsList
    appendItems constantsList
    appendItemVariable
    
    where appendItems :: ExpWriter s => [s] -> IO ()
          appendItems [] = return ()
          appendItems (x:xs) = do
              item <- menuItemNewWithLabel $ unpack $ tRepr x
              onActivateLeaf item (writeExp x box)
              menuShellAppend menu item
              appendItems xs
              
          appendItemVariable = do
              item <- menuItemNewWithLabel "Variable"
              onActivateLeaf item (writeVarExp box)
              menuShellAppend menu item
              

writeQuantifier ::  (BoxClass b) => Quantifier -> b -> IO ()
writeQuantifier q box = do
    label_init  <- labelNew (Just (quantInit ++ (unpack $ tRepr q)))
    entry_var   <- entryNew
    label_dots1 <- labelNew (Just ":")
    box_sub_expr1 <- hBoxNew False 10
    label_dots2 <- labelNew (Just ":")
    box_sub_expr2 <- hBoxNew False 10
    label_end   <- labelNew (Just quantEnd)
    
    createButtonSubExpr box_sub_expr1
    createButtonSubExpr box_sub_expr2
    
    widgetSetSizeRequest entry_var 10 (-1)
    
    boxPackStart box label_init PackGrow 0
    boxPackStart box entry_var PackGrow 0
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

writeOperator ::  (BoxClass b) => Operator -> b -> IO ()
writeOperator o box = 
    case opNotationTy o of
        NPrefix -> do
            box_sub_expr <- hBoxNew False 10
            createButtonSubExpr box_sub_expr
            label <- labelNew (Just (unpack $ tRepr o))
            boxPackStart box label PackGrow 0
            boxPackStart box box_sub_expr PackGrow 0
            widgetShowAll box
             
        NInfix -> do
            box_sub_expr1 <- hBoxNew False 10
            createButtonSubExpr box_sub_expr1
            box_sub_expr2 <- hBoxNew False 10
            createButtonSubExpr box_sub_expr2
            label <- labelNew (Just (unpack $ tRepr o))
            boxPackStart box box_sub_expr1 PackGrow 0
            boxPackStart box label PackGrow 0
            boxPackStart box box_sub_expr2 PackGrow 0
            widgetShowAll box
            
        NPostfix -> do
            box_sub_expr <- hBoxNew False 10
            createButtonSubExpr box_sub_expr
            label <- labelNew (Just (unpack $ tRepr o))
            boxPackStart box box_sub_expr PackGrow 0
            boxPackStart box label PackGrow 0
            widgetShowAll box

writeConstant :: (BoxClass b) => Constant -> b -> IO ()
writeConstant c box = do
    label <- labelNew (Just (unpack $ tRepr c))
    boxPackStart box label PackGrow 0
    widgetShowAll box

-- packWidgets ::(BoxClass box, WidgetClass child) =>
--               box -> [child] -> Packing -> Int -> IO () 
-- packWidgets b [] p i = return ()
-- packWidgets b (x:xs) p i = do
--     boxPackStart b x p i
--     packWidgets b xs p i

writeVarExp :: (BoxClass b) => b -> IO ()
writeVarExp box = do
    entry <- entryNew
    widgetSetSizeRequest entry 10 (-1)
    removeAllChilds box
    boxPackStart box entry PackGrow 0
    widgetShowAll box
    

removeAllChilds :: (BoxClass b) => b -> IO ()
removeAllChilds b = containerForeach b (removeChild b)
    where removeChild :: (BoxClass b,WidgetClass child) => b -> child -> IO ()
          removeChild b c = containerRemove b c


createButtonSubExpr :: (BoxClass b) => b -> IO ()
createButtonSubExpr box = do
    button_sub_expr <- buttonNewWithLabel "Expresión"
    boxPackStart box button_sub_expr PackGrow 0
    menu_symbols <- menuNew
    loadItems menu_symbols box
    onPressed button_sub_expr (menuPopup menu_symbols Nothing)
    widgetShowAll menu_symbols