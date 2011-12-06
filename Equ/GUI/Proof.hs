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
import Equ.PreExpr
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
newProofRef :: ExprWidget -> TreeView -> TreeView -> HBox -> StatusPlace -> IO ProofRef
newProofRef w symbolList axiomList axiom_box st_place= do
    ref <- newRef $ ProofState { proof = emptyProof $ head $ relationList
                        , validProof = Right $ emptyProof $ head $ relationList
                        , symCtrl = symbolList
                        , focusedExpr = ExprFocus { expr = emptyExpr
                                                  , path = (id,id)
                                                  , inpFocus = formBox w
                                        }
                        , modifExpr = updateStart
                        , status = st_place
                        , axiomCtrl = axiomList
                        , axiomBox = axiom_box
                    }
    return ref

{- Setea los eventos de un widget de expresion. La funcion f es la que se utiliza
para actualizar la expresion dentro de la prueba
-}
eventsExprWidget :: HBox -> ProofRef -> HBox -> ExprWidget -> (Proof -> Focus -> Proof) -> String ->
                    ListStore (String,HBox -> IRProof) -> IO ()
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
                    --eventFocusIn
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
    
    hboxInit    <- hBoxNew False 2
    boxExprWidget1 <- hBoxNew False 2
    exprWidget1 <- createExprWidget boxExprWidget1
    --addStep1    <- buttonNewWithLabel "Agregar Paso ↓"
    widgetSetSizeRequest hboxInit (-1) 30
    separator1 <- vSeparatorNew
    -- boxPackStart hboxInit boxExprWidget1 PackGrow 3
    boxPackStart hboxInit separator1 PackNatural 8
    --boxPackStart hboxInit addStep1 PackNatural 3
    
    
    -- Caja central para colocar la relacion y el axioma aplicado
    center_box  <- hBoxNew False 2
    
    -- Relation combo Box
    (combo_rel,store_rel)   <- newComboRel
    comboBoxSetActive combo_rel 0
    axiom_box   <- hBoxNew False 2
    widgetSetSizeRequest combo_rel 80 (-1)
    boxPackStart center_box combo_rel PackNatural 5
    boxPackStart center_box axiom_box PackGrow 5
    
    
    -- Consideramos que inicialmente la primera expresion está enfocada, por eso
    -- construimos la referencia inicial con esa caja.
    proofRef <- newProofRef exprWidget1 symbolList axiomList axiom_box st_place
    (flip evalStateT proofRef $ 
         getAxiomCtrl >>=
        (flip eventsTruthList aListStore))

    combo_rel `on` changed $ evalStateT (changeItem combo_rel store_rel) proofRef

    
    eventsExprWidget hboxInit proofRef boxExprWidget1 exprWidget1 updateStart "start" sListStore
    
    hboxEnd     <- hBoxNew False 2
    boxExprWidget2 <- hBoxNew False 2
    exprWidget2 <- createExprWidget boxExprWidget2
    --addStep2    <- buttonNewWithLabel "Agregar Paso ↑"
    widgetSetSizeRequest hboxEnd (-1) 30
    separator2 <- vSeparatorNew
    -- boxPackStart hboxEnd boxExprWidget2 PackGrow 3
    boxPackStart hboxEnd separator2 PackNatural 8
    --boxPackStart hboxEnd addStep2 PackNatural 3
    
    eventsExprWidget hboxEnd proofRef boxExprWidget2 exprWidget2 updateEnd "end" sListStore
    
    boxPackStart ret_box hboxInit PackNatural 2
    boxPackStart ret_box center_box PackNatural 2
    boxPackStart ret_box hboxEnd PackNatural 2
    
    valid_button <- buttonNewWithLabel "Validar prueba"
    valid_string <- labelNew (Just "")
    boxPackStart ret_box valid_button PackNatural 20
    boxPackStart ret_box valid_string PackNatural 20
                            
    valid_button `on` buttonPressEvent $ tryEvent $
                            eventWithState (checkProof valid_string) proofRef
    
    widgetShowAll ret_box
    
    
    where changeItem c list = do 
            ind <- liftIO $ comboBoxGetActive c
            newRel <- liftIO $ listStoreGetValue list ind
            updateRelation newRel
            
        
        
checkProof valid_string = getProof >>= 
             \p -> (let vp = validateProof p in
                case vp of
                     Right _ -> liftIO $ labelSetText valid_string "PRUEBA VALIDA"
                     Left err -> setErrMessage "No se puede aplicar el axioma"
                )
                
    
    
    
    
    