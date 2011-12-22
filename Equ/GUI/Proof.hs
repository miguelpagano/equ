-- | Aspectos de la interfaz independientes de las expresiones.
module Equ.GUI.Proof where

import Equ.GUI.Types
import Equ.GUI.Utils
import Equ.GUI.Settings
import Equ.GUI.SymbolList
import Equ.GUI.TruthList
import Equ.Rule
import Equ.Theories
import Equ.Proof
import Equ.PreExpr hiding (goDownL,goDownR,goRight,goUp)
import Equ.GUI.Widget
import Equ.GUI.Expr
import Equ.Parser

import Graphics.UI.Gtk hiding (eventButton, eventSent,get)
import qualified Graphics.UI.Gtk as G
import Graphics.UI.Gtk.Gdk.EventM
import Graphics.UI.Gtk.Glade (GladeXML,xmlGetWidget)
import Data.Reference
import Data.Maybe(fromJust)
import Control.Monad.Trans(lift,liftIO)
import Control.Monad.State(get,evalStateT)
import Data.Text(unpack)
import Data.Map(empty)
import Data.List(elemIndex)
import Data.Either(rights)


-- | Crea una nueva referencia
newProofRef :: HBox -> TreeView -> TreeView -> HBox -> StatusPlace -> IO ProofRef
newProofRef boxExpr symbolList axiomList axiom_box st_place= do
    ref <- newRef $ ProofState { proof = emptyProof $ head $ relationList
                        , validProof = Right $ holeProof $ head $ relationList
                        , symCtrl = symbolList
                        , focusedExpr = ExprFocus { expr = emptyExpr
                                                  , path = (id,id)
                                                  , inpFocus = boxExpr
                                        }
                        , modifExpr = updateStartFocus
                        , status = st_place
                        , axiomCtrl = axiomList
                        , axiomBox = axiom_box
                    }
    return ref

                    
loadProof :: Proof -> VBox -> ProofRef -> ListStore (String,HBox -> IRProof) -> IO ()
loadProof p ret_box proofRef sListStore = do
    
    hboxInit <- createExprWidget (toExpr $ fromRight $ getStart p) proofRef updateFirstExpr "" sListStore
    hboxEnd  <- createExprWidget (toExpr $ fromRight $ getEnd p) proofRef updateFinalExpr "" sListStore
    center_box <- vBoxNew False 2
    
    boxPackStart ret_box hboxInit PackNatural 2
    boxPackStart ret_box center_box PackNatural 2
    boxPackStart ret_box hboxEnd PackNatural 2
    
    completeProof p center_box proofRef goTop sListStore
    
    evalStateT (updateProof $ toProofFocus p) proofRef


completeProof :: Proof -> VBox -> ProofRef -> (ProofFocus -> Maybe ProofFocus) ->
                 ListStore (String,HBox -> IRProof) -> IO ()
completeProof p@(Trans _ rel f1 fm f2 p1 p2) center_box proofRef moveFocus ls = do
    (boxL,boxR) <- newStepProof (toExpr fm) proofRef moveFocus center_box ls
    
    completeProof p1 boxL proofRef (goDownL . fromJust . moveFocus) ls
    completeProof p2 boxR proofRef (goDownR . fromJust . moveFocus) ls  
completeProof (Hole _ rel f1 f2) center_box proofRef moveFocus ls = do
    createCenterBox center_box proofRef moveFocus ls rel Nothing
completeProof p@(Simple _ rel f1 f2 b) center_box proofRef moveFocus ls = do
    createCenterBox center_box proofRef moveFocus ls rel (Just b)
    
    
createNewProof :: (Maybe Proof) -> VBox ->  TreeView -> ListStore (String,HBox -> IRProof) -> TreeView -> 
                  ListStore (String,HBox -> IRProof) -> StatusPlace -> IO ()
createNewProof maybe_proof ret_box symbolList sListStore axiomList aListStore st_place= do
    putStrLn "creando prueba..."
    
    -- delete all children
    containerForeach ret_box $ \x -> containerRemove ret_box x >> widgetDestroy x

    -- TODO: Ver si está bien poner cajas vacias para la caja de expresion y la de 
    -- axiomas al iniciar la referencia. Si el usuario elige un símbolo para construir 
    -- expresión o elige un axioma ANTES de hacer click en alguna caja, entonces la prueba
    -- se actualiza en el estado pero no se muestra en la interfaz (ya que esas cajas vacías
    -- nunca fueron agregadas a la interfaz)
    
    -- inicialmente ponemos una caja vacia en el foco, asumiendo que no hay ninguna
    -- expresión enfocada.
    empty_box1 <- hBoxNew False 2
    empty_box2 <- hBoxNew False 2
    proofRef <- newProofRef empty_box1 symbolList axiomList empty_box2 st_place
    
    -- Caja central para colocar la relacion y el axioma aplicado. La funcion para mover el foco
    -- es ir hasta el tope.
    center_box <- vBoxNew False 2
    createCenterBox center_box proofRef goTop sListStore (head relationList) Nothing

    
    (flip evalStateT proofRef $ 
         getAxiomCtrl >>=
        (flip eventsTruthList aListStore))

    case maybe_proof of
         Nothing -> do
            hboxInit <- createExprWidget holeExpr proofRef updateFirstExpr "start" sListStore
            hboxEnd  <- createExprWidget holeExpr proofRef updateFinalExpr "end" sListStore

            boxPackStart ret_box hboxInit PackNatural 2
            boxPackStart ret_box center_box PackNatural 2
            boxPackStart ret_box hboxEnd PackNatural 2
         Just p -> loadProof p ret_box proofRef sListStore
    
    
    
    valid_button <- buttonNewWithLabel "Validar prueba"
    validImage <- imageNewFromStock stockCancel IconSizeSmallToolbar
    validProofHBox <- hBoxNew False 2
    boxPackStart validProofHBox valid_button PackGrow 5
    boxPackStart validProofHBox validImage PackNatural 5
    
    boxPackStart ret_box validProofHBox PackNatural 20
    
    save_button <- buttonNewWithLabel "Guardar Prueba"
    
    boxPackStart ret_box save_button PackNatural 20
    
    valid_button `on` buttonPressEvent $ tryEvent $
                            eventWithState (checkProof validImage) proofRef
                            
    save_button `on` buttonPressEvent $ tryEvent $
                            eventWithState saveProofDialog proofRef
                            
    widgetShowAll ret_box
            

-- TODO: VER DONDE METER ESTAS FUNCIONES
updateFirstExpr pf f = updateStartFocus (fromJust $ goTop pf) f
updateFinalExpr pf f = updateEndFocus (fromJust $ goTop pf) f
        
checkProof validImage = getProof >>= 
    \pf -> (let vp = validateProof (toProof pf) in
                case vp of
                     Right _ -> liftIO $ imageSetFromStock validImage stockOk IconSizeSmallToolbar
                     Left err -> setErrMessage (show err) >> 
                                 liftIO (putStrLn $ show err) >> 
                                 liftIO (imageSetFromStock validImage stockCancel IconSizeSmallToolbar)
                )
                
saveProofDialog :: IRProof
saveProofDialog = do
    dialog <- liftIO $ fileChooserDialogNew (Just "Guardar Prueba") Nothing FileChooserActionSave 
                                   [("Guardar",ResponseAccept),("Cancelar",ResponseCancel)]
    response <- liftIO $ dialogRun dialog
    
    case response of
         ResponseAccept -> do
             selected <- liftIO $ fileChooserGetFilename dialog
             liftIO $ putStrLn ("aceptar clicked. Selected is " ++ show selected)
             case selected of
                  Just filepath -> saveProof filepath >> (liftIO $ widgetDestroy dialog)
                  Nothing -> liftIO $ widgetDestroy dialog
         _ -> liftIO $ widgetDestroy dialog
                
saveProof :: FilePath -> IRProof
saveProof filepath = do
    getProof >>= \pf -> liftIO $ encodeFile filepath (toProof pf)

createCenterBox :: VBox -> ProofRef -> (ProofFocus -> Maybe ProofFocus) -> 
                   ListStore (String,HBox -> IRProof) -> Relation -> Maybe Basic -> IO ()
createCenterBox center_box proofRef moveFocus symbolList rel maybe_basic = do
    
    containerForeach center_box $ \x -> containerRemove center_box x >> widgetDestroy x
    
    hbox <- hBoxNew False 2
    
    -- Relation combo Box
    (combo_rel,store_rel)   <- newComboRel rel
    
    -- Axiom box
    axiom_box   <- hBoxNew False 2
    widgetSetSizeRequest axiom_box 450 (-1)
    label <- labelNew (Just $ "?")
    boxPackStart axiom_box label PackGrow 0

    addStepButton <- buttonNewWithLabel "Agregar Paso ↓"
    widgetSetSizeRequest combo_rel 80 (-1)
    boxPackStart hbox combo_rel PackNatural 5
    eb_axiom_box <- eventBoxNew
    set eb_axiom_box [ containerChild := axiom_box ]
    boxPackStart hbox eb_axiom_box PackNatural 5
    boxPackStart hbox addStepButton PackNatural 5

    combo_rel `on` changed $ evalStateT (changeItem combo_rel store_rel axiom_box) proofRef
    
    eb_axiom_box `on` enterNotifyEvent $ tryEvent $ highlightBox hbox hoverBg
                                                    
    eb_axiom_box `on` leaveNotifyEvent $ tryEvent $ (liftIO $ widgetGetStyle hbox) >>=
                                \st -> (liftIO $ styleGetBackground st (toEnum 0)) >>=
                                \bg -> unlightBox hbox bg
    
    eb_axiom_box `on` buttonPressEvent $ tryEvent $ do
        LeftButton <- eventButton
        liftIO $ putStrLn "axiom_box clicked"
        eventWithState (changeProofFocus moveFocus axiom_box) proofRef
        
    eb_axiom_box `on` buttonPressEvent $ tryEvent $ do
        RightButton <- eventButton
        liftIO $ putStrLn "axiom_box right clicked"
        eventWithState (changeProofFocus moveFocus axiom_box) proofRef
        liftIO $ containerForeach axiom_box $ \x -> containerRemove axiom_box x >> widgetDestroy x
        label <- liftIO (labelNew (Just $ "?"))
        liftIO $ boxPackStart axiom_box label PackGrow 0
        eventWithState (getProof >>= \pf ->
                        updateProof (toHoleProof pf)
            ) proofRef
        liftIO $ widgetShowAll axiom_box
        
    addStepButton `on` buttonPressEvent $ 
                        liftIO (newStepProof holeExpr proofRef moveFocus center_box symbolList) >>
                        return False
        
        
    boxPackStart center_box hbox PackNatural 5
    
    case maybe_basic of 
         Nothing -> return ()
         Just basic -> evalStateT (writeTruth basic axiom_box) proofRef
    
    return ()
        
    where changeItem c list box = do 
            changeProofFocus moveFocus box
            ind <- liftIO $ comboBoxGetActive c
            newRel <- liftIO $ listStoreGetValue list ind
            updateRelation newRel

newStepProof :: PreExpr -> ProofRef -> (ProofFocus -> Maybe ProofFocus) ->
                VBox -> ListStore (String,HBox -> IRProof) -> IO (VBox,VBox)
newStepProof expr proofRef moveFocus container symbolList = do
    containerForeach container $ \x -> containerRemove container x >> widgetDestroy x
    
    (flip evalStateT proofRef $ 
        -- Movemos el ProofFocus hasta donde está el hueco que queremos reemplazar
        -- por una transitividad
        getProof >>= \pf -> updateProof (fromJust $ moveFocus pf) >>
        -- Reemplazamos el hueco por una transitividad
        getProof >>= \pf -> updateProof (addEmptyStep pf) >>
        -- Dejamos enfocada la prueba derecha de la transitividad
        getProof >>= \pf -> updateProof (fromJust $ goDownR pf))
    
    relation <- evalStateT (getProof >>= \(proof,_) -> 
                            return (fromRight $ getRel proof)) proofRef
    centerBoxL <- vBoxNew False 2
    createCenterBox centerBoxL proofRef (goDownL . fromJust . moveFocus) symbolList relation Nothing
    centerBoxR <- vBoxNew False 2
    createCenterBox centerBoxR proofRef (goDownR . fromJust . moveFocus) symbolList relation Nothing
    exprBox <- createExprWidget expr proofRef updateFocus "?" symbolList
    
    boxPackStart container centerBoxL PackNatural 5
    boxPackStart container exprBox PackNatural 5
    boxPackStart container centerBoxR PackNatural 5
        
    widgetShowAll container
    
    return (centerBoxL,centerBoxR)
    
    {- Cuando se modifique la expresion que queda en el medio de esta transitividad,
       tenemos que actualizar la expr del medio de la transitividad, la expr final de la
       prueba izquierda y la expr inicial de la prueba derecha. Para hacer todo esto vamos moviéndonos
       con el zipper
       -}
    where updateFocus pf f = updateMiddleFocus (fromJust $ moveFocus pf) f >>= \pf' ->
                             updateEndFocus (fromJust $ goDownL pf') f >>= \pf'' ->
                             updateStartFocus (fromJust $ goRight pf'') f
            
relationListStore :: IO (ListStore Relation)
relationListStore = listStoreNew relationList 
                      
newComboRel :: Relation -> IO (ComboBox,ListStore Relation)
newComboRel rel = do
    list <- relationListStore
    combo <- comboBoxNew
    renderer <- cellRendererTextNew
    cellLayoutPackStart combo renderer False
    cellLayoutSetAttributes combo renderer list (\ind -> [cellText := unpack $ relRepr ind])
    comboBoxSetModel combo (Just list)
    selectRelation rel combo list
    return (combo,list)
            
selectRelation :: Relation -> ComboBox -> ListStore Relation -> IO ()
selectRelation r combo lstore = do
    ls <- listStoreToList lstore
    comboBoxSetActive combo (getIndexFromList ls r)
    
    where getIndexFromList ls rel = fromJust $ elemIndex rel ls

            
createExprWidget :: PreExpr -> ProofRef -> (ProofFocus -> Focus -> Maybe ProofFocus) -> 
                    String -> ListStore (String,HBox -> IRProof) -> IO HBox
              
createExprWidget expr proofRef fUpdateFocus fname sListStore = do
    
    
    hbox    <- hBoxNew False 2
    boxExprWidget <- hBoxNew False 2
    
    label <- labelNew (Just "Expresión:")
    widgetSetSizeRequest label 80 (-1)
    scrolled <- scrolledWindowNew Nothing Nothing
    box <- hBoxNew False 2
    scrolledWindowAddWithViewport scrolled box
    button_apply <- buttonNewFromStock stockApply
    button_clear <- buttonNewFromStock stockClear
    --widgetSetSizeRequest button_apply (-1) 30
    button_box <- hButtonBoxNew
    widgetSetSizeRequest button_box 200 (-1)
    --widgetSetSizeRequest button_box 20 (-1)
    --boxPackStart button_box button_apply PackNatural 2
    boxPackStart button_box button_clear PackNatural 2
    boxPackStart boxExprWidget label PackNatural 1
    boxPackStart boxExprWidget scrolled PackGrow 1
    boxPackStart boxExprWidget button_box PackNatural 1
    
    widgetSetSizeRequest hbox (-1) 30
    
    exprWidget <- return $ ExprWidget { extBox = boxExprWidget -- Box externa
                        , expLabel = label
                        , formBox = box
                        , clearButton = button_clear
                        , applyButton = button_apply
    }
    
    eventsExprWidget hbox proofRef boxExprWidget exprWidget fUpdateFocus fname sListStore
    
    flip evalStateT proofRef $
        writeExprWidget expr box
    
    return hbox   

{- Setea los eventos de un widget de expresion. La funcion f es la que se utiliza
para actualizar la expresion dentro de la prueba
-}
eventsExprWidget :: HBox -> ProofRef -> HBox -> ExprWidget -> (ProofFocus -> Focus -> Maybe ProofFocus) 
                    -> String -> ListStore (String,HBox -> IRProof) -> IO ()
eventsExprWidget ext_box proofRef hb w f fname sListStore =
    
    flip evalStateT proofRef $ 
        liftIO setupFocusEvent >>
        setupForm (formBox w) >>
        getSymCtrl >>=
        (flip eventsSymbolList sListStore) >>
        liftIO ((clearButton w) `on` buttonPressEvent $ tryEvent $ 
                            eventWithState (clearFocus (formBox w) >> return ()) 
                            proofRef) >> return ()
    
    where setupFocusEvent = do
                eb <- eventBoxNew
                set eb [ containerChild := hb ]
                boxPackStart ext_box eb PackGrow 0
                eb `on` buttonReleaseEvent $ do
                    -- movemos el proofFocus hasta donde está esta expresión.
                    eventWithState (updateModifExpr f) proofRef
                    liftIO $ putStrLn fname
                    liftIO $ widgetShowAll eb
                    return False

                    
fromRight = head . rights . return          
