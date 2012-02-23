-- | Modulo de muestra y control de eventos sobre pruebas.
module Equ.GUI.Proof where

import Equ.GUI.Types hiding (GState)
import Equ.GUI.State 
import Equ.GUI.State.Expr
import Equ.GUI.Utils
import Equ.GUI.Proof.RelationList

import Equ.GUI.Settings
import Equ.GUI.TruthList
import Equ.Rule
import Equ.Theories
import Equ.Proof
import Equ.PreExpr hiding (goDownL,goDownR,goRight,goUp,goTop)
import qualified Equ.PreExpr.Show as PS
import Equ.GUI.Widget
import Equ.GUI.Expr ( writeExprWidget,setupForm
                    , newExprState, reloadExpr
                    , createExprWidget
                    , setupOptionExprWidget 
                    )
import Equ.Parser
import Equ.Types

import Graphics.UI.Gtk hiding (eventButton, eventSent,get)
import qualified Graphics.UI.Gtk as G
import Graphics.UI.Gtk.Gdk.EventM
import Graphics.UI.Gtk.Glade (GladeXML,xmlGetWidget)
import Graphics.UI.Gtk.Display.Image

import Data.Maybe(fromJust)
import Data.Text(unpack)
import Data.Map(empty)
import Data.List(elemIndex)

import Control.Monad.Reader
import Control.Applicative((<$>))
import qualified Data.Foldable as F (forM_,mapM_)

-- | Crea una nueva referencia
newProofState :: (Maybe Proof) -> HBox -> ExprWidget -> ExprWidget ->
                 ProofStepWidget -> IState ProofState
newProofState (Just p) axiom_box expr1W expr2W proofW= return pr
    where
        pr :: ProofState
        pr = ProofState { proof = toProofFocus p
                        , validProof = validateProof p
                        , axiomBox = axiom_box
                        , proofWidget = (pw,Top)
                        , proofAnnots = emptyProofAnnots
                        }
                        
        pw = Simple () () expr1W expr2W proofW
            
            
newProofState Nothing axiom_box expr1W expr2W proofW = getGlobalCtx >>=
                                  return . pr . Just
    where
        pr :: Maybe Ctx -> ProofState
        pr c = ProofState { proof = p c
                          , validProof = validateProof $ toProof (p c)
                          , axiomBox = axiom_box
                          , proofWidget = (pw,Top)
                          , proofAnnots = emptyProofAnnots
                        }
        p c = emptyProof c $ head $ relationList
        
        pw = Simple () () expr1W expr2W proofW

                        
-- | Carga una prueba a la interfaz. 
loadProof :: Proof -> VBox -> VBox -> ExprWidget -> ProofStepWidget -> IState ()
loadProof p ret_box truthBox initExprWidget proofStepW = do
    
    newExpr_w  <- newExprWidget (toExpr $ fromRight $ getEnd p) (ProofMove moveToEnd) truthBox
    
    empty_box1 <- io $ hBoxNew False 2
    proof <- newProofState (Just p) empty_box1 initExprWidget newExpr_w proofStepW
    updateProofState proof
    
    -- Expresión inicial:
    removeAllChildren (formBox initExprWidget)
    initExpr <- return . fromRight $ getStart p
    
    labelInitExpr <- io $ labelNew (Just $ PS.showExpr $ toExpr initExpr)
    io $ boxPackStart (formBox initExprWidget) labelInitExpr PackNatural 2
    io $ widgetShowAll (formBox initExprWidget)
    
    io (boxPackStart ret_box truthBox PackNatural 2 >>
        boxPackStart ret_box (extBox newExpr_w) PackNatural 2)
    
    completeProof p truthBox truthBox (ProofMove goTop)
    
    
completeProof :: Proof -> VBox -> VBox -> ProofMove -> IState ()
completeProof (Hole _ rel f1 f2) center_box top_box  moveFocus =
    --addStepProof center_box top_box moveFocus Nothing >>
    return ()

completeProof p@(Simple _ rel f1 f2 b) center_box top_box moveFocus =
    --addStepProof center_box top_box moveFocus (Just b) >>
    changeProofFocusAndShow (pm moveFocus) (pm moveFocus) (pm moveFocus) Nothing >>
    getProofWidget >>= \pfw ->
    writeTruth b (axiomWidget $ fromJust $ getBasicFocus pfw) >>
    return ()

completeProof p@(Trans _ rel f1 fm f2 p1 p2) center_box top_box moveFocus = do
    (boxL,boxR) <- newStepProof (toExpr fm) moveFocus center_box top_box
    
    completeProof p1 boxL top_box (ProofMove (goDownL . fromJust . pm moveFocus))
    completeProof p2 boxR top_box (ProofMove (goDownR . fromJust . pm moveFocus))

-- | Crea toda la estructura necesaria para una nueva prueba.  Si el
-- primer argumento es @Nothing@, entonces se crea la estructura para
-- una prueba vacía; si es @Just p@, entonces se crea para la prueba @p@.
createNewProof :: (Maybe Proof) -> VBox -> VBox -> ExprWidget -> IState ()
createNewProof proof ret_box truthBox initExprWidget = do
    io $ debug "creando prueba..."
    
    -- delete all children
    removeAllChildren ret_box
    
    removeAllChildren (formBox initExprWidget)
    initExpr <- getExpr
    
    labelInitExpr <- io $ labelNew (Just $ PS.showExpr $ toExpr initExpr)
    io $ boxPackStart (formBox initExprWidget) labelInitExpr PackNatural 2 >>
         widgetShowAll (formBox initExprWidget)
    
    -- truthBox es la caja central para colocar la relacion y el axioma aplicado. La
    -- funcion para mover el foco es ir hasta el tope.
    io $ debug $ "Antes de crear el widget de paso de prueba"
    
    firstStepProof <- addStepProof truthBox truthBox (ProofMove goTop)  Nothing
    
    io $ debug $ "Pude crear el widget de paso de prueba"
        
    maybe (emptyProof truthBox initExprWidget firstStepProof) 
          (\p -> loadProof p ret_box truthBox initExprWidget firstStepProof) proof
    
    s <- get    
    io $ widgetShowAll ret_box

    where emptyProof box initExprW firstStepW = do
            --hboxInit <- createExprWidget holePreExpr goTopbox
            expr_w  <- newExprWidget holePreExpr (ProofMove moveToEnd) box

            initState initExprW expr_w firstStepW
            
            io (--boxPackStart ret_box hboxInit PackNatural 2 >>
                boxPackStart ret_box box PackNatural 2 >>
                boxPackStart ret_box (extBox expr_w) PackNatural 2
               )


initState :: ExprWidget -> ExprWidget -> ProofStepWidget -> IRG
initState expr1W expr2W proofW = do
    -- TODO: Ver si está bien poner cajas vacias para la caja de expresion y la de 
    -- axiomas al iniciar la referencia. Si el usuario elige un símbolo para construir 
    -- expresión o elige un axioma ANTES de hacer click en alguna caja, entonces la prueba
    -- se actualiza en el estado pero no se muestra en la interfaz (ya que esas cajas vacías
    -- nunca fueron agregadas a la interfaz)
    
    -- inicialmente ponemos una caja vacia en el foco, asumiendo que no hay ninguna
    -- expresión enfocada.
    empty_box1 <- io $ hBoxNew False 2
    initExpr <- getExpr
    proof' <- newProofState (Just $ pr initExpr) empty_box1 expr1W expr2W proofW
    updateProofState proof'

    where pr e= flip newProofWithStart e $ head $ relationList
    
checkProof :: Image -> VBox -> IState ()
checkProof validImage top_box = getProofState >>= (F.mapM_ $ \ps ->
                                updateValidProof >> checkValidProof >>= \valid ->
                                if valid 
                                then updateImageValid iconValidProof
                                else getValidProof >>= \(Left errorProof) ->
                                        io (putStrLn (show errorProof)) >>
                                        updateImageValid iconErrorProof >>
                                        reportErrWithErrPaned (show errorProof))
                                       

-- | Creación de línea de justificación de paso en una prueba.
addStepProof :: VBox -> VBox -> ProofMove -> Maybe Basic -> IState ProofStepWidget
addStepProof center_box top_box moveFocus maybe_basic = do
    -- top_box es la caja central mas general, que es creada al iniciar una prueba.    
    removeAllChildren center_box
    
    rel <- getRelPF
    hbox <- io $ hBoxNew False 2
    
    -- Relation combo Box
    (combo_rel,store_rel)   <- io $ newComboRel rel
    
    -- Axiom box
    axiom_box  <- io $ hBoxNew False 2
    label      <- io $ labelNew (Just $ emptyLabel)
    io (widgetSetSizeRequest axiom_box 450 (-1) >>
        boxPackStart axiom_box label PackGrow 0)

    button_box <- io $ hButtonBoxNew    
    addStepProofButton <- io $ makeButtonWithImage addStepIcon
    io $ buttonSetRelief addStepProofButton ReliefNone
    
    io $ setToolTip addStepProofButton "Agregar Paso"
    io $ widgetSetSizeRequest button_box 150 (-1)
    
    eb_axiom_box <- io $ eventBoxNew 
    
    imageValidStep <- io $ imageNewFromStock iconUnknownProof IconSizeSmallToolbar

    io (widgetSetSizeRequest combo_rel 80 (-1) >>
        boxPackStart button_box addStepProofButton PackNatural 2 >>
        boxPackStart hbox combo_rel PackNatural 5 >>
        set eb_axiom_box [ containerChild := axiom_box ] >>
        boxPackStart hbox eb_axiom_box PackGrow 5 >> 
        boxPackStart hbox button_box PackNatural 1 >>
        boxPackStart hbox imageValidStep PackNatural 1 >>
        highlightBox hbox axiomBg)

    s <- get
    io (combo_rel `on` changed $ evalStateT (changeItem combo_rel store_rel axiom_box) s)

    addHandler eb_axiom_box buttonPressEvent (do
        LeftButton <- eventButton
        io $ debug "axiom_box clicked"
        eventWithState (changeProofFocusAndShow (pm moveFocus) (pm moveFocus) (pm moveFocus) (Just axiom_box)) s)
        
        
    addHandler eb_axiom_box  buttonPressEvent (do
        RightButton <- eventButton
        io $ debug "axiom_box right clicked"
        eventWithState (changeProofFocusAndShow (pm moveFocus) (pm moveFocus) (pm moveFocus) (Just axiom_box) >>
                        removeAllChildren axiom_box) s

        label <- io (labelNew (Just $ emptyLabel))
        io $ boxPackStart axiom_box label PackGrow 0
        eventWithState (getProof >>= updateProofUndo . toHoleProof) s
        io $ widgetShowAll axiom_box)
        
    io $ addStepProofButton `on` buttonPressEvent $ 
       flip eventWithState s (newStepProof holePreExpr moveFocus center_box top_box) >>
       return False
        
        
    io $ boxPackStart center_box hbox PackNatural 5
    
    flip F.mapM_ maybe_basic $ flip writeTruth axiom_box

    return ProofStepWidget {
                    relation = (combo_rel,store_rel) 
                  , axiomWidget = axiom_box 
                  , addStepButton = addStepProofButton
                  , validImage = imageValidStep
                  , stepBox = hbox
    }
            
    where changeItem c list box = do 
            changeProofFocusAndShow (pm moveFocus) (pm moveFocus) (pm moveFocus) (Just box)
            ind <- io $ comboBoxGetActive c
            newRel <- io $ listStoreGetValue list ind
            updateRelation newRel
            validateStep
      
unSelectBox :: IRG      
unSelectBox = getStepProofBox >>= F.mapM_ (\box -> unlightBox box (Just axiomBg))

selectBox :: Color -> IRG
selectBox color = getStepProofBox >>= F.mapM_ (\box -> highlightBox box color)
                          
                                 
newStepProof :: PreExpr -> ProofMove -> VBox -> VBox -> IState (VBox,VBox)
newStepProof expr moveFocus container top_box = do

    removeAllChildren container

    -- Movemos el ProofFocus hasta donde está el hueco que queremos reemplazar
    -- por una transitividad
    changeProofFocusAndShow (pm moveFocus) (pm moveFocus) (pm moveFocus) Nothing
        -- Reemplazamos el hueco por una transitividad
    pf <- getProof

    pfa <- getProofAnnots
    
    updateProofUndo (addEmptyStep pf) 
    updateProofAnnots (addEmptyStepAnnots pfa)
    
    relation <- getRelPF
    
    centerBoxL <- io $vBoxNew False 2
    newStepWL <- addStepProof centerBoxL top_box (ProofMove (goDownL . fromJust . pm moveFocus)) Nothing
    centerBoxR <- io $ vBoxNew False 2
    newStepWR <- addStepProof centerBoxR top_box (ProofMove (goDownR . fromJust . pm moveFocus)) Nothing
    expr_w <- newExprWidget expr (ProofMove moveFocus') top_box
    
    io $ boxPackStart container centerBoxL PackNatural 5 >>
         boxPackStart container (extBox expr_w) PackNatural 5 >>
         boxPackStart container centerBoxR PackNatural 5 >>        
         widgetShowAll container
           
    (pfW,path) <- getProofWidget
    updateProofWidget (Trans () () (fromJust' $ getStartFocus (pfW,path)) expr_w (fromJust' $ getEndFocus (pfW,path)) 
                      (Simple () () (fromJust' $ getStartFocus (pfW,path)) expr_w newStepWL) 
                      (Simple () () expr_w (fromJust' $ getEndFocus (pfW,path)) newStepWR)
                      , path)
                      
    -- Dejamos enfocada la prueba derecha de la transitividad
    changeProofFocusAndShow goDownR goDownR goDownR Nothing           
    

    return (centerBoxL,centerBoxR)
    
    {- Cuando se modifique la expresion que queda en el medio de esta transitividad,
       tenemos que actualizar la expr del medio de la transitividad, la expr final de la
       prueba izquierda y la expr inicial de la prueba derecha. Para hacer todo esto vamos moviéndonos
       con el zipper
       -}
    where moveFocus' = Just . goEnd . fromJust . goDownL . fromJust . pm moveFocus
          
          fromJust' = maybe (error "CONSTRUYENDO Trans para widget") id
            
            
newExprWidget :: PreExpr -> ProofMove -> VBox -> IState ExprWidget              
newExprWidget expr moveFocus top_box = do

    exprWidget <- createExprWidget False
    
    eventsExprWidget expr top_box moveFocus exprWidget 
    flip runEnvBox (exprWidget,id,moveFocus) (writeExprWidget (formBox exprWidget) expr) 

    return exprWidget
    
-- | Setea los eventos de un widget de expresion. La funcion f es la
-- que se utiliza para actualizar la expresion dentro de la prueba
eventsExprWidget :: PreExpr -> VBox -> ProofMove -> ExprWidget -> IState ()
eventsExprWidget expr top_box moveFocus exprWidget = do
    s <- get 
    win <- getWindow
    io (setupFocusEvent s)
    flip runEnvBox (exprWidget,id,moveFocus) $
             setupOptionExprWidget win >>
             setupForm (formBox exprWidget) Editable
    io $ widgetShowAll (extBox exprWidget)
    return ()
    
    where hb = extBox exprWidget
          setupFocusEvent :: GRef -> IO ()
          setupFocusEvent s = do
            
            -- MIGUEL: ¿por qué manejamos este evento? Esto causa un bug
            -- en la edición de expresiones con la barra de símbolos.
            -- ¡Si no está, entonces tenemos un bug con la edición con
            -- el teclado!
            hb `on` buttonReleaseEvent $ do
                    flip eventWithState s $
                    -- movemos el proofFocus hasta donde está esta expresión.
                         updateExprWidget exprWidget >>
                         changeProofFocus'
                    io (widgetShowAll hb)
                    return True

            flip F.mapM_ (choicesButton exprWidget) $ \ choices -> 
                 do choices `on` buttonPressEvent $ tryEvent $
                            eventWithState (changeProofFocus' >> showChoices) s
                    return ()

          changeProofFocus' = changeProofFocusAndShow (pm moveFocus) (pm moveFocus) (pm moveFocus) Nothing >>
--                               io (proofFocusToBox path top_box) >>= \center_box ->
--                               io (axiomBoxFromCenterBox center_box) >>= \axiom_box ->
--                               changeProofFocus moveFocus moveFocus (Just axiom_box) >>
                              updateSelectedExpr -- Actualizamos la expresion seleccionada
                        
          showChoices = do
            menu <- io menuNew
            pf <- getProof
            exp1 <- return . fromJust $ getStartFocus pf
            m_axiom <- return $ getBasicFocus pf
            flip F.mapM_ m_axiom $ \axiom -> 
                return (possibleExpr (toExpr exp1) axiom) >>=
                addToMenu menu >>
                io (widgetShowAll menu >> menuPopup menu Nothing)
            
          addToMenu m = mapM_ addItem
            where addItem e = do
                    item <- io $ menuItemNewWithLabel $ PS.showExpr e
                    io $ menuShellAppend m item
                    s' <- get
                    io $ item `on` buttonPressEvent $ tryEvent $
                             flip eventWithState s' $ 
                                  -- Actualizamos la expresion
                                  changeProofFocus' >>
                                  updateExprWidget exprWidget >>
                                  runEnvBox (writeExprWidget (formBox exprWidget) e) (exprWidget, id,moveFocus) >>
                                  updateExpr e id



-- | Descarta la prueba actual.
discardProof centralBox expr_w = unsetProofState >>
                                 removeAllChildren centralBox >>
                                 getExpr >>= \e ->
                                 runEnvBox (reloadExpr (toExpr e)) (expr_w,id,ProofMove Just)
                                        
changeProofFocusAndShow moveFocus moveFocusAnnots moveFocusW box = 
                                 unSelectBox >>
                                 changeProofFocus moveFocus moveFocusAnnots moveFocusW box >>
                                 selectBox focusBg
