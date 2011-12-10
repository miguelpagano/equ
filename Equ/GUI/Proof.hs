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
                    
relationListStore :: IO (ListStore Relation)
relationListStore = listStoreNew relationList 
                      
newComboRel :: IO (ComboBox,ListStore Relation)
newComboRel = do
    list <- relationListStore
    combo <- comboBoxNew
    renderer <- cellRendererTextNew
    cellLayoutPackStart combo renderer False
    cellLayoutSetAttributes combo renderer list (\ind -> [cellText := unpack $ relRepr ind])
    comboBoxSetModel combo (Just list)
    return (combo,list)


createNewProof :: VBox ->  TreeView -> ListStore (String,HBox -> IRProof) -> TreeView -> 
                  ListStore (String,HBox -> IRProof) -> StatusPlace -> IO ()
createNewProof ret_box symbolList sListStore axiomList aListStore st_place= do
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
    center_box  <- createCenterBox proofRef goTop sListStore

    
    (flip evalStateT proofRef $ 
         getAxiomCtrl >>=
        (flip eventsTruthList aListStore))


    hboxInit <- createExprWidget proofRef updateStartFocus "start" sListStore
    hboxEnd  <- createExprWidget proofRef updateEndFocus "end" sListStore
    
    boxPackStart ret_box hboxInit PackNatural 2
    boxPackStart ret_box center_box PackNatural 2
    boxPackStart ret_box hboxEnd PackNatural 2
    
    valid_button <- buttonNewWithLabel "Validar prueba"
    validImage <- imageNewFromStock stockCancel IconSizeSmallToolbar
    validProofHBox <- hBoxNew False 2
    boxPackStart validProofHBox valid_button PackGrow 5
    boxPackStart validProofHBox validImage PackNatural 5
    
    boxPackStart ret_box validProofHBox PackNatural 20
    
    valid_button `on` buttonPressEvent $ tryEvent $
                            eventWithState (checkProof validImage) proofRef
    
    
--     center_box `on` buttonReleaseEvent $ tryEvent $
--                             eventWithState (liftIO $ putStrLn "center box clicked") proofRef

    {-
    addStepButton `on` buttonPressEvent $ tryEvent $ 
                        eventWithState (-}
                            
    
    
    widgetShowAll ret_box
            
        
        
checkProof validImage = getProof >>= 
    \pf -> (let vp = validateProof (toProof pf) in
                case vp of
                     Right _ -> liftIO $ imageSetFromStock validImage stockOk IconSizeSmallToolbar
                     Left err -> setErrMessage (show err) >> 
                                 liftIO (imageSetFromStock validImage stockCancel IconSizeSmallToolbar)
                )

newStepProof :: ProofRef -> (ProofFocus -> Maybe ProofFocus) ->
                VBox -> ListStore (String,HBox -> IRProof) -> IO ()
newStepProof proofRef moveFocus container symbolList = do
    containerForeach container $ \x -> containerRemove container x >> widgetDestroy x
    
    centerBoxL <- createCenterBox proofRef (goDownL . fromJust . moveFocus) symbolList
    centerBoxR <- createCenterBox proofRef (goDownR . fromJust . moveFocus) symbolList
    exprBox <- createExprWidget proofRef updateFocus "?" symbolList
    
    boxPackStart container centerBoxL PackNatural 5
    boxPackStart container exprBox PackNatural 5
    boxPackStart container centerBoxR PackNatural 5
    
    (flip evalStateT proofRef $ 
        -- Movemos el ProofFocus:
        getProof >>= \pf -> updateProof (fromJust $ moveFocus pf) >>
        -- Reemplazamos el hueco por una transitividad
        getProof >>= \pf -> updateProof (addEmptyStep pf))
        
    widgetShowAll container
    
    
    where updateFocus pf f = updateEndFocus (fromJust $ goDownL $ fromJust $ moveFocus pf) f >>= \pf' ->
                             updateStartFocus (fromJust $ goRight pf') f >>= \pf'' ->
                             updateMiddleFocus (fromJust $ goUp pf'') f
                
    
createCenterBox :: ProofRef -> (ProofFocus -> Maybe ProofFocus) -> 
                   ListStore (String,HBox -> IRProof) -> IO VBox
createCenterBox proofRef moveFocus symbolList= do
    -- Caja central para colocar la relacion y el axioma aplicado
    center_box  <- vBoxNew False 2
    
    hbox <- hBoxNew False 2
    
    -- Relation combo Box
    (combo_rel,store_rel)   <- newComboRel
    comboBoxSetActive combo_rel 0
    
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

    combo_rel `on` changed $ evalStateT (changeItem combo_rel store_rel) proofRef
    
    eb_axiom_box `on` buttonReleaseEvent $ do
        liftIO $ putStrLn "axiom_box clicked"
        eventWithState (getProof >>= \pf -> updateProof (fromJust $ moveFocus pf) >>
                        updateAxiomBox axiom_box) proofRef
        return False

    addStepButton `on` buttonPressEvent $ 
                        liftIO (newStepProof proofRef moveFocus center_box symbolList) >>
                        return False
        
        
    boxPackStart center_box hbox PackNatural 5
    
    return center_box
        
    where changeItem c list = do 
            ind <- liftIO $ comboBoxGetActive c
            newRel <- liftIO $ listStoreGetValue list ind
            updateRelation newRel
    
createExprWidget :: ProofRef -> (ProofFocus -> Focus -> Maybe ProofFocus) -> String -> 
              ListStore (String,HBox -> IRProof) -> IO HBox
              
createExprWidget proofRef fUpdateFocus fname sListStore = do
    
    
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
    
    return hbox   
    