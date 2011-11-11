-- | Aspectos de la interfaz independientes de las expresiones.
module Equ.GUI.Proof where

import Equ.GUI.Types
import Equ.GUI.Utils
import Equ.GUI.Settings
import Equ.GUI.SymbolList
import Equ.Rule
import Equ.Theories
import Equ.Proof
import Equ.PreExpr
import Equ.GUI.Widget
import Equ.GUI.Expr

import Graphics.UI.Gtk hiding (eventButton, eventSent,get)
import qualified Graphics.UI.Gtk as G
import Graphics.UI.Gtk.Gdk.EventM
import Graphics.UI.Gtk.Glade (GladeXML,xmlGetWidget)
import Data.Reference
import Data.Maybe(fromJust)
import Control.Monad.Trans(lift,liftIO)
import Control.Monad.State(get,evalStateT)
import Data.Text(unpack)




createFormWidget :: HBox -> IO FormWidget
createFormWidget ext_box = do
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
    boxPackStart button_box button_apply PackNatural 2
    boxPackStart button_box button_clear PackNatural 2
    boxPackStart ext_box label PackNatural 1
    boxPackStart ext_box scrolled PackGrow 1
    boxPackStart ext_box button_box PackNatural 1
    return $ FormWidget { extBox = ext_box -- Box externa
                        , expLabel = label
                        , formBox = box
                        , clearButton = button_clear
                        , applyButton = button_apply
    }
    
newProofRef :: FormWidget -> TreeView -> TreeView -> StatusPlace -> IO ProofRef
newProofRef w symbolList axiomList st_place= do
    ref <- newRef $ ProofState { proof = emptyProof $ head $ relationList
                        , symCtrl = symbolList
                        , focusedExpr = ExprFocus { expr = emptyExpr
                                                  , path = (id,id)
                                                  , inpFocus = formBox w
                                        }
                        , modifExpr = updateStart
                        , status = st_place
                        , axiomCtrl = axiomList
                    }
    return ref

{- Setea los eventos de un widget de expresion. La funcion f es la que se utiliza
para actualizar la expresion dentro de la prueba
-}
eventsFormWidget :: HBox -> ProofRef -> HBox -> FormWidget -> (Proof -> Focus -> Proof) -> String ->
                    ListStore (String,HBox -> IRProof) -> IO ()
eventsFormWidget ext_box proofRef hb w f fname sListStore =
    
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
                eb `on` enterNotifyEvent $ do
                    --eventFocusIn
                    eventWithState (updateModifExpr f) proofRef
                    liftIO $ putStrLn fname
                    liftIO $ widgetShowAll eb
                    return False
                    
relationListStore :: IO (ListStore Relation)
relationListStore = listStoreNew relationList 
                      
newComboRel :: IO ComboBox
newComboRel = do
    list <- relationListStore
    combo <- comboBoxNew
    renderer <- cellRendererTextNew
    cellLayoutPackStart combo renderer False
    cellLayoutSetAttributes combo renderer list (\ind -> [cellText := unpack $ relRepr ind])
    comboBoxSetModel combo (Just list)
    return combo

newAxiomBox :: IO Label
newAxiomBox = labelNew (Just "Axioma")

createNewProof :: VBox ->  TreeView -> ListStore (String,HBox -> IRProof) -> TreeView -> StatusPlace -> IO ()
createNewProof ret_box symbolList sListStore axiomList st_place= do
    putStrLn "creando prueba..."
    
    hboxInit    <- hBoxNew False 2
    boxFormWidget1 <- hBoxNew False 2
    formWidget1 <- createFormWidget boxFormWidget1
    addStep1    <- buttonNewWithLabel "Agregar Paso ↓"
    widgetSetSizeRequest hboxInit (-1) 30
    separator1 <- vSeparatorNew
    -- boxPackStart hboxInit boxFormWidget1 PackGrow 3
    boxPackStart hboxInit separator1 PackNatural 8
    boxPackStart hboxInit addStep1 PackNatural 3
    
    -- Consideramos que inicialmente la primera expresion está enfocada, por eso
    -- construimos la referencia inicial con esa caja.
    proofRef <- newProofRef formWidget1 symbolList axiomList st_place
    eventsFormWidget hboxInit proofRef boxFormWidget1  formWidget1 updateStart "start" sListStore
    
    hboxEnd     <- hBoxNew False 2
    boxFormWidget2 <- hBoxNew False 2
    formWidget2 <- createFormWidget boxFormWidget2
    addStep2    <- buttonNewWithLabel "Agregar Paso ↑"
    widgetSetSizeRequest hboxEnd (-1) 30
    separator2 <- vSeparatorNew
    -- boxPackStart hboxEnd boxFormWidget2 PackGrow 3
    boxPackStart hboxEnd separator2 PackNatural 8
    boxPackStart hboxEnd addStep2 PackNatural 3
    
    eventsFormWidget hboxEnd proofRef boxFormWidget2 formWidget2 updateEnd "end" sListStore
    
    center_box  <- hBoxNew False 2
    combo_rel   <- newComboRel
    axiom_box   <- newAxiomBox
    widgetSetSizeRequest combo_rel 80 (-1)
    boxPackStart center_box combo_rel PackNatural 5
    boxPackStart center_box axiom_box PackGrow 5
    
    boxPackStart ret_box hboxInit PackNatural 2
    boxPackStart ret_box center_box PackNatural 2
    boxPackStart ret_box hboxEnd PackNatural 2
    widgetShowAll ret_box
