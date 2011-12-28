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
import Equ.GUI.Expr (clearFocus,writeExprWidget)
import Equ.Parser
import Equ.Types

import Graphics.UI.Gtk hiding (eventButton, eventSent,get)
import qualified Graphics.UI.Gtk as G
import Graphics.UI.Gtk.Gdk.EventM
import Graphics.UI.Gtk.Glade (GladeXML,xmlGetWidget)
import Graphics.UI.Gtk.Display.Image
import Data.Reference
import Data.Maybe(fromJust)
import Control.Monad.Trans(lift,liftIO)
import Control.Monad.State(get,evalStateT)
import Data.Text(unpack)
import Data.Map(empty)
import Data.List(elemIndex)
import Data.Either(rights)


-- | Crea una nueva referencia
newProofState :: (Maybe Proof) -> HBox -> IState ProofState
newProofState (Just p) axiom_box = return pr
    where
        pr :: ProofState
        pr = ProofState { proof = toProofFocus p
                        , validProof = Right p
                        , modifExpr = updateStartFocus
                        , axiomBox = axiom_box
                        }
newProofState Nothing axiom_box = return pr
    where
        pr :: ProofState
        pr = ProofState { proof = emptyProof $ head $ relationList
                        , validProof = Right $ holeProof $ head $ relationList
                        , modifExpr = updateStartFocus
                        , axiomBox = axiom_box
                        }

newExprState :: HBox -> HBox -> IState ExprState
newExprState hbox1 hbox2 = do
    return eState
    where 
        eState = ExprState { fExpr = emptyExpr
                           , pathExpr = (id,id)
                           , eventExpr = hbox1
                           , fType = TyUnknown
                           , eventType = hbox2
        }
                            
    
                        
                        
-- | Carga una prueba a la interfaz
loadProof :: Proof -> VBox -> GRef -> ListStore (String,HBox -> IRG) -> IO ()
loadProof p ret_box ref sListStore = do
    
    hboxInit <- createExprWidget (toExpr $ fromRight $ getStart p) ref updateFirstExpr getFirstExpr "" sListStore
    hboxEnd  <- createExprWidget (toExpr $ fromRight $ getEnd p) ref updateFinalExpr getFinalExpr "" sListStore
    center_box <- vBoxNew False 2
    
    boxPackStart ret_box hboxInit PackNatural 2
    boxPackStart ret_box center_box PackNatural 2
    boxPackStart ret_box hboxEnd PackNatural 2
    
    completeProof p center_box ref goTop sListStore

completeProof :: Proof -> VBox -> GRef -> (ProofFocus -> Maybe ProofFocus) ->
                 ListStore (String,HBox -> IRG) -> IO ()
completeProof p@(Trans _ rel f1 fm f2 p1 p2) center_box proofRef moveFocus ls = do
    (boxL,boxR) <- newStepProof (toExpr fm) proofRef moveFocus center_box ls
    
    completeProof p1 boxL proofRef (goDownL . fromJust . moveFocus) ls
    completeProof p2 boxR proofRef (goDownR . fromJust . moveFocus) ls  
completeProof (Hole _ rel f1 f2) center_box proofRef moveFocus ls = do
    createCenterBox center_box proofRef moveFocus ls rel Nothing
completeProof p@(Simple _ rel f1 f2 b) center_box proofRef moveFocus ls = do
    createCenterBox center_box proofRef moveFocus ls rel (Just b)
                        
createNewProof :: (Maybe Proof) -> VBox ->  ListStore (String,HBox -> IRG) -> 
                                   ListStore (String,HBox -> IRG) -> IState ()
createNewProof maybe_proof ret_box sListStore aListStore = do
    s <- get
    liftIO $ putStrLn "creando prueba..."
    
    -- delete all children
    liftIO $ containerForeach ret_box $ \x -> containerRemove ret_box x >> widgetDestroy x

    -- TODO: Ver si está bien poner cajas vacias para la caja de expresion y la de 
    -- axiomas al iniciar la referencia. Si el usuario elige un símbolo para construir 
    -- expresión o elige un axioma ANTES de hacer click en alguna caja, entonces la prueba
    -- se actualiza en el estado pero no se muestra en la interfaz (ya que esas cajas vacías
    -- nunca fueron agregadas a la interfaz)
    
    -- inicialmente ponemos una caja vacia en el foco, asumiendo que no hay ninguna
    -- expresión enfocada.
    empty_box1 <- liftIO $ hBoxNew False 2
    proof' <- newProofState Nothing empty_box1
    updateProofState proof'
    
    hbox1 <- liftIO $ hBoxNew False 2
    hbox2 <- liftIO $ hBoxNew False 2
    expr' <- newExprState hbox1 hbox2
    updateExprState expr'

   -- Caja central para colocar la relacion y el axioma aplicado. La funcion para mover el foco
    -- es ir hasta el tope.
    center_box <- liftIO $ vBoxNew False 2
    liftIO $ createCenterBox center_box s goTop sListStore (head relationList) Nothing
    
    (getAxiomCtrl >>= flip eventsTruthList aListStore)

    case maybe_proof of
         Nothing -> do
            hboxInit <- liftIO $ createExprWidget holeExpr s updateFirstExpr getFirstExpr "start" sListStore
            hboxEnd  <- liftIO $ createExprWidget holeExpr s updateFinalExpr getFinalExpr "end" sListStore

            liftIO $ boxPackStart ret_box hboxInit PackNatural 2
            liftIO $ boxPackStart ret_box center_box PackNatural 2
            liftIO $ boxPackStart ret_box hboxEnd PackNatural 2
         Just p -> do
            empty_box1 <- liftIO $ hBoxNew False 2
            ps <- newProofState (Just p) empty_box1
            updateProofState ps 
            liftIO $ loadProof p ret_box s sListStore
    
    valid_button <- liftIO $ buttonNewWithLabel "Validar prueba"
    validImage <- liftIO $ imageNewFromStock stockCancel IconSizeSmallToolbar
    validProofHBox <- liftIO $ hBoxNew False 2
    liftIO $ boxPackStart validProofHBox valid_button PackGrow 5
    liftIO $ boxPackStart validProofHBox validImage PackNatural 5
    
    liftIO $ boxPackStart ret_box validProofHBox PackNatural 20
    
    liftIO $ (valid_button `on` buttonPressEvent $ tryEvent $
                            eventWithState (checkProof validImage) s)

    liftIO $ widgetShowAll ret_box

-- TODO: VER DONDE METER ESTAS FUNCIONES
updateFirstExpr pf f = updateStartFocus (fromJust $ goTop pf) f
updateFinalExpr pf f = updateEndFocus (fromJust $ goTop pf) f

getFirstExpr pf = fromJust $ getStartFocus (fromJust $ goTop pf)
getFinalExpr pf = fromJust $ getEndFocus (fromJust $ goTop pf)

checkProof :: Image -> IState ()
checkProof validImage = getProof >>= \pf ->
                          case validateProof (toProof pf) of
                            Right _ -> liftIO $ imageSetFromStock validImage stockOk IconSizeSmallToolbar
                            Left err -> reportErrWithErrPaned (show err) >> liftIO (
                                       putStrLn (show err) >>
                                       imageSetFromStock validImage stockCancel IconSizeSmallToolbar)

createCenterBox :: VBox -> GRef -> (ProofFocus -> Maybe ProofFocus) -> 
                   ListStore (String,HBox -> IRG) -> Relation -> Maybe Basic -> IO ()
createCenterBox center_box ref moveFocus symbolList rel maybe_basic = do
    
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

    combo_rel `on` changed $ evalStateT (changeItem combo_rel store_rel axiom_box) ref

    eb_axiom_box `on` enterNotifyEvent $ tryEvent $ highlightBox hbox hoverBg
                                                    
    eb_axiom_box `on` leaveNotifyEvent $ tryEvent $ (liftIO $ widgetGetStyle hbox) >>=
                                \st -> (liftIO $ styleGetBackground st (toEnum 0)) >>=
                                \bg -> unlightBox hbox bg
    
    eb_axiom_box `on` buttonPressEvent $ tryEvent $ do
        LeftButton <- eventButton
        liftIO $ putStrLn "axiom_box clicked"
        eventWithState (changeProofFocus moveFocus axiom_box) ref
        
    eb_axiom_box `on` buttonPressEvent $ tryEvent $ do
        RightButton <- eventButton
        liftIO $ putStrLn "axiom_box right clicked"
        eventWithState (changeProofFocus moveFocus axiom_box) ref
        liftIO $ containerForeach axiom_box $ \x -> containerRemove axiom_box x >> widgetDestroy x
        label <- liftIO (labelNew (Just $ "?"))
        liftIO $ boxPackStart axiom_box label PackGrow 0
        eventWithState (getProof >>= \pf ->
                        updateProof (toHoleProof pf)
            ) ref
        liftIO $ widgetShowAll axiom_box
        
    addStepButton `on` buttonPressEvent $ 
                        liftIO (newStepProof holeExpr ref moveFocus center_box symbolList) >>
                        return False
        
        
    boxPackStart center_box hbox PackNatural 5
    
    case maybe_basic of 
         Nothing -> return ()
         Just basic -> evalStateT (writeTruth basic axiom_box) ref
    
    return ()
        
    where changeItem c list box = do 
            changeProofFocus moveFocus box
            ind <- liftIO $ comboBoxGetActive c
            newRel <- liftIO $ listStoreGetValue list ind
            updateRelation newRel

newStepProof :: PreExpr -> GRef -> (ProofFocus -> Maybe ProofFocus) ->
                VBox -> ListStore (String,HBox -> IRG) -> IO (VBox,VBox)
newStepProof expr ref moveFocus container symbolList = do
    containerForeach container $ \x -> containerRemove container x >> widgetDestroy x
    
    (flip evalStateT ref $ 
        -- Movemos el ProofFocus hasta donde está el hueco que queremos reemplazar
        -- por una transitividad
        getProof >>= \pf -> updateProof (fromJust $ moveFocus pf) >>
        -- Reemplazamos el hueco por una transitividad
        getProof >>= \pf -> updateProof (addEmptyStep pf) >>
        -- Dejamos enfocada la prueba derecha de la transitividad
        getProof >>= \pf -> updateProof (fromJust $ goDownR pf))
    
    relation <- evalStateT (getProof >>= \(proof,_) -> 
                            return (fromRight $ getRel proof)) ref
    
    centerBoxL <- vBoxNew False 2
    createCenterBox centerBoxL ref (goDownL . fromJust . moveFocus) symbolList relation Nothing
    centerBoxR <- vBoxNew False 2
    createCenterBox centerBoxR ref (goDownR . fromJust . moveFocus) symbolList relation Nothing
    exprBox <- createExprWidget expr ref updateFocus (fromJust . getFocus) "?" symbolList
    
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
                             
          getFocus pf = moveFocus pf >>= \pf' ->
                        goDownR pf' >>= \pf'' ->
                        getStartFocus pf''


            
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

            
createExprWidget :: PreExpr -> GRef -> (ProofFocus -> Focus -> Maybe ProofFocus) -> 
                    (ProofFocus -> Focus) -> String -> ListStore (String,HBox -> IRG) -> IO HBox
              
createExprWidget expr ref fUpdateFocus fGetFocus fname sListStore = do
    
    
    hbox    <- hBoxNew False 2
    boxExprWidget <- hBoxNew False 2
    
    label <- labelNew (Just "Expresión:")
    -- widgetSetSizeRequest label 80 (-1)
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
    -- boxPackStart boxExprWidget label PackNatural 1
    boxPackStart boxExprWidget scrolled PackGrow 1
    boxPackStart boxExprWidget button_box PackNatural 1
    
    widgetSetSizeRequest hbox (-1) 50
    
    exprWidget <- return $ ExprWidget { extBox = boxExprWidget -- Box externa
                                     , expLabel = label
                                     , formBox = box
                                     , clearButton = button_clear
                                     , applyButton = button_apply
                                     }
    
    eventsExprWidget hbox ref boxExprWidget exprWidget fUpdateFocus fGetFocus fname sListStore
    
    flip evalStateT ref $ writeExprWidget expr box
    
    return hbox   

    
{- Setea los eventos de un widget de expresion. La funcion f es la que se utiliza
para actualizar la expresion dentro de la prueba
-}
eventsExprWidget :: HBox -> GRef -> HBox -> ExprWidget -> (ProofFocus -> Focus -> Maybe ProofFocus) 
                    -> (ProofFocus -> Focus) -> String -> ListStore (String,HBox -> IRG) -> IO ()
eventsExprWidget ext_box proofRef hb w fUpdate fGet fname sListStore =
    
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
                    eventWithState (updateModifExpr fUpdate >>
                                    updateSelectedExpr fGet) proofRef
                    liftIO $ putStrLn fname
                    liftIO $ widgetShowAll eb
                    return False

                    
fromRight = head . rights . return          
