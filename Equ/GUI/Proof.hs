-- | Aspectos de la interfaz independientes de las expresiones.
module Equ.GUI.Proof where

import Equ.GUI.Types
import Equ.GUI.State
import Equ.GUI.Utils

import Equ.GUI.Settings
import Equ.GUI.SymbolList
import Equ.GUI.TruthList
import Equ.Rule
import Equ.Theories
import Equ.Proof
import Equ.PreExpr hiding (goDownL,goDownR,goRight,goUp,goTop)
import Equ.GUI.Widget
import Equ.GUI.Expr (clearFocus,writeExprWidget,setupForm,makeOptionEvent)
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

import Control.Monad((=<<))
import qualified Data.Foldable as F (forM_,mapM_)

-- | Crea una nueva referencia
newProofState :: (Maybe Proof) -> HBox -> IState ProofState
newProofState (Just p) axiom_box = return pr
    where
        pr :: ProofState
        pr = ProofState { proof = toProofFocus p
                        , validProof = validateProof p
                        , modifExpr = updateStartFocus
                        , axiomBox = axiom_box
                        }
newProofState Nothing axiom_box = return pr
    where
        pr :: ProofState
        pr = ProofState { proof = p
                        , validProof = validateProof (toProof p)
                        , modifExpr = updateStartFocus
                        , axiomBox = axiom_box
                        }
        p = emptyProof $ head $ relationList
                        
                        
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
loadProof :: Proof -> VBox -> VBox -> GRef -> IO ()
loadProof p ret_box center_box ref = do
    
    empty_box1 <- hBoxNew False 2
    evalStateT (newProofState (Just p) empty_box1 >>= updateProofState) ref
    
    hboxInit <- createExprWidget (toExpr $ fromRight $ getStart p) ref goTop updateFirstExpr getFirstExpr center_box
    hboxEnd  <- createExprWidget (toExpr $ fromRight $ getEnd p) ref moveToEnd updateFinalExpr getFinalExpr center_box
    
    boxPackStart ret_box hboxInit PackNatural 2
    boxPackStart ret_box center_box PackNatural 2
    boxPackStart ret_box hboxEnd PackNatural 2
    
    completeProof p center_box center_box ref goTop

moveToEnd :: ProofFocus -> Maybe ProofFocus
moveToEnd pf = Just $ goEnd (goTop' pf)
    
    
completeProof :: Proof -> VBox -> VBox -> GRef -> (ProofFocus -> Maybe ProofFocus)
                 -> IO ()
completeProof p@(Trans _ rel f1 fm f2 p1 p2) center_box top_box proofRef moveFocus = do
    (boxL,boxR) <- newStepProof (toExpr fm) proofRef moveFocus center_box top_box
    
    completeProof p1 boxL top_box proofRef (goDownL . fromJust . moveFocus)
    completeProof p2 boxR top_box proofRef (goDownR . fromJust . moveFocus)  
completeProof (Hole _ rel f1 f2) center_box top_box proofRef moveFocus = do
    createCenterBox center_box top_box proofRef moveFocus rel Nothing
completeProof p@(Simple _ rel f1 f2 b) center_box top_box proofRef moveFocus = do
    createCenterBox center_box top_box proofRef moveFocus rel (Just b)
                        
createNewProof :: (Maybe Proof) -> VBox -> IState ()
createNewProof maybe_proof ret_box = do
    s <- get
    liftIO $ debug "creando prueba..."
    
    -- delete all children
    liftIO $ containerForeach ret_box $ \x -> containerRemove ret_box x >> widgetDestroy x
    
    initState

   -- Caja central para colocar la relacion y el axioma aplicado. La funcion para mover el foco
    -- es ir hasta el tope.
    center_box <- liftIO $ vBoxNew False 2
    liftIO $ createCenterBox center_box center_box s goTop (head relationList) Nothing
    
    case maybe_proof of
         Nothing -> do
            hboxInit <- liftIO $ createExprWidget holePreExpr s goTop updateFirstExpr getFirstExpr center_box
            hboxEnd  <- liftIO $ createExprWidget holePreExpr s moveToEnd updateFinalExpr getFinalExpr center_box

            liftIO $ boxPackStart ret_box hboxInit PackNatural 2
            liftIO $ boxPackStart ret_box center_box PackNatural 2
            liftIO $ boxPackStart ret_box hboxEnd PackNatural 2
         Just p -> do
            liftIO $ loadProof p ret_box center_box s
    
    valid_button <- liftIO $ buttonNewWithLabel "Validar prueba"
    validImage <- liftIO $ imageNewFromStock stockCancel IconSizeSmallToolbar
    validProofHBox <- liftIO $ hBoxNew False 2
    liftIO $ boxPackStart validProofHBox valid_button PackGrow 5
    liftIO $ boxPackStart validProofHBox validImage PackNatural 5
    
    liftIO $ boxPackStart ret_box validProofHBox PackNatural 20
    
    liftIO $ (valid_button `on` buttonPressEvent $ tryEvent $
                            eventWithState (checkProof validImage center_box) s)

    liftIO $ widgetShowAll ret_box

initState :: IRG
initState = do
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
    
    
-- TODO: VER DONDE METER ESTAS FUNCIONES
-- TODO: Comprobar que el cambio no afecta la semántica.
updateFirstExpr pf f = goTop pf >>= flip updateStartFocus f
updateFinalExpr pf f = goTop pf >>= flip updateEndFocus f

-- TODO: Hacer que estas funciones devuelvan Maybes y manejar
-- apropiadamente los casos Nothing en los lugares que se usan.
getFirstExpr = fromJust . getStartFocus . fromJust . goTop
getFinalExpr = fromJust . getEndFocus . fromJust . goTop

checkProof :: Image -> VBox -> IState ()
checkProof validImage top_box = updateValidProof >> checkValidProof >>= \valid ->
                                if valid 
                                then liftIO (img stockOk)
                                else getValidProof >>= \(Left errorProof) ->
                                      liftIO (putStrLn (show errorProof) >>
                                              img stockCancel) >>
                                       reportErrWithErrPaned (show errorProof) >>
                                       unSelectBox >>
                                       getProof >>= \pf ->
                                       return ((getMoveFocus errorProof) (goTop' pf)) >>=
                                       \pf -> selectBox pf errBg top_box
    where img icon = imageSetFromStock validImage icon IconSizeSmallToolbar
                                       

createCenterBox :: VBox -> VBox -> GRef -> (ProofFocus -> Maybe ProofFocus) -> 
                   Relation -> Maybe Basic -> IO ()
createCenterBox center_box top_box ref moveFocus rel maybe_basic = do
    -- top_box es la caja central mas general, que es creada al iniciar una prueba.
    
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

    --eb_axiom_box `on` enterNotifyEvent $ tryEvent $ highlightBox hbox hoverBg
                                                    
    {-eb_axiom_box `on` leaveNotifyEvent $ tryEvent $ (liftIO $ widgetGetStyle hbox) >>=
                                \st -> (liftIO $ styleGetBackground st (toEnum 0)) >>=
                                \bg -> unlightBox hbox (Just bg) -}
    
    eb_axiom_box `on` buttonPressEvent $ tryEvent $ do
        LeftButton <- eventButton
        liftIO $ debug "axiom_box clicked"
        eventWithState (unSelectBox >>
                        changeProofFocus moveFocus (Just axiom_box) >>
                        getProof >>= \pf ->
                        selectBox pf focusBg top_box
                        ) ref
        
        
    eb_axiom_box `on` buttonPressEvent $ tryEvent $ do
        RightButton <- eventButton
        liftIO $ debug "axiom_box right clicked"
        eventWithState (changeProofFocus moveFocus (Just axiom_box)) ref
        liftIO $ containerForeach axiom_box $ \x -> containerRemove axiom_box x >> widgetDestroy x
        label <- liftIO (labelNew (Just $ "?"))
        liftIO $ boxPackStart axiom_box label PackGrow 0
        eventWithState (getProof >>= \pf ->
                        updateProof (toHoleProof pf)
            ) ref
        liftIO $ widgetShowAll axiom_box
        
    addStepButton `on` buttonPressEvent $ 
                        liftIO (newStepProof holePreExpr ref moveFocus center_box top_box) >>
                        return False
        
        
    boxPackStart center_box hbox PackNatural 5
    
    F.mapM_ (\basic -> evalStateT (writeTruth basic axiom_box) ref) maybe_basic
            
    where changeItem c list box = do 
            unSelectBox
            changeProofFocus moveFocus (Just box)
            pf <- getProof
            selectBox pf focusBg top_box
            ind <- liftIO $ comboBoxGetActive c
            newRel <- liftIO $ listStoreGetValue list ind
            updateRelation newRel
      
unSelectBox :: IRG      
unSelectBox = getAxiomBox >>= \ axiom_box ->
            liftIO (widgetGetParent axiom_box) >>= \ eb_box ->
            F.forM_ eb_box 
                        (\ p -> liftIO (widgetGetParent p) >>=
                        flip unlightBox Nothing . castToHBox . fromJust
                        )

selectBox :: ProofFocus -> Color -> VBox -> IRG
selectBox (_,path) color top_box = liftIO (proofFocusToBox path top_box) >>= \cbox ->
            liftIO (containerGetChildren cbox) >>= \chd ->
                highlightBox (castToHBox $ chd!!0) color
                                 
newStepProof :: PreExpr -> GRef -> (ProofFocus -> Maybe ProofFocus) ->
                VBox -> VBox -> IO (VBox,VBox)
newStepProof expr ref moveFocus container top_box = do
    containerForeach container $ \x -> containerRemove container x >> widgetDestroy x
    
    (flip evalStateT ref $ 
        -- Movemos el ProofFocus hasta donde está el hueco que queremos reemplazar
        -- por una transitividad
        getProof >>= \pf -> changeProofFocus moveFocus Nothing >>
        -- Reemplazamos el hueco por una transitividad
        getProof >>= \pf -> updateProof (addEmptyStep pf) >>
        -- Dejamos enfocada la prueba derecha de la transitividad
        getProof >>= \pf -> changeProofFocus goDownR Nothing )
    
    relation <- evalStateT (getProof >>= \(proof,_) -> 
                            return (fromRight $ getRel proof)) ref
    
    centerBoxL <- vBoxNew False 2
    createCenterBox centerBoxL top_box ref (goDownL . fromJust . moveFocus) relation Nothing
    centerBoxR <- vBoxNew False 2
    createCenterBox centerBoxR top_box ref (goDownR . fromJust . moveFocus) relation Nothing
    exprBox <- createExprWidget expr ref moveFocus' updateFocus (fromJust . getFocus) top_box
    
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

          moveFocus' = (Just . goEnd . fromJust . goDownL . fromJust . moveFocus)
            
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

            
createExprWidget :: PreExpr -> GRef -> (ProofFocus -> Maybe ProofFocus) ->
                    (ProofFocus -> Focus -> Maybe ProofFocus) -> 
                    (ProofFocus -> Focus) -> VBox -> IO HBox
              
createExprWidget expr ref moveFocus fUpdateFocus fGetFocus top_box = do

    hbox    <- hBoxNew False 2
    boxExprWidget <- hBoxNew False 2
    
    label <- labelNew (Just "Expresión:")
    -- widgetSetSizeRequest label 80 (-1)
    --scrolled <- scrolledWindowNew Nothing Nothing
    box <- hBoxNew False 2
    --scrolledWindowAddWithViewport scrolled box
    button_apply <- buttonNewFromStock stockApply
    button_clear <- buttonNewFromStock stockClear
    expr_choices <- buttonNewWithLabel "▼"
    widgetSetSizeRequest button_apply (-1) 30
    button_box <- hButtonBoxNew
    widgetSetSizeRequest button_box 200 (-1)
    
    -- boxPackStart button_box button_apply PackNatural 2
    boxPackStart button_box expr_choices PackNatural 2
    --boxPackStart button_box button_clear PackNatural 2
    -- boxPackStart boxExprWidget label PackNatural 1
    boxPackStart boxExprWidget box PackGrow 1
    boxPackStart boxExprWidget button_box PackNatural 1
    
    widgetSetSizeRequest hbox (-1) 50
    
    exprWidget <- return $ ExprWidget { extBox = boxExprWidget -- Box externa
                                      , expLabel = label
                                      , formBox = box
                                      , clearButton = button_clear
                                      , applyButton = button_apply
                                      , choicesButton = expr_choices
                                      }
    
    eventsExprWidget expr hbox ref boxExprWidget exprWidget moveFocus fUpdateFocus fGetFocus top_box
    
    flip evalStateT ref $ writeExprWidget expr box
    
    return hbox
    
{- Setea los eventos de un widget de expresion. La funcion f es la que se utiliza
para actualizar la expresion dentro de la prueba
-}
eventsExprWidget :: PreExpr -> HBox -> GRef -> HBox -> ExprWidget -> 
                    (ProofFocus -> Maybe ProofFocus) ->
                    (ProofFocus -> Focus -> Maybe ProofFocus) ->
                    (ProofFocus -> Focus) -> VBox -> IO ()
eventsExprWidget expr ext_box proofRef hb w moveFocus fUpdate fGet top_box =
    
    flip evalStateT proofRef $ 
        getWindow >>= \win ->
        setupOptionExprWidget win expr >>
        liftIO setupFocusEvent >>
        setupForm (formBox w) >>
        liftIO ((clearButton w) `on` buttonPressEvent $ tryEvent $ 
                            eventWithState (clearFocus (formBox w) >> return ()) 
                            proofRef) >> return ()
    
    where 
        setupFocusEvent :: IO (ConnectId Button)
        setupFocusEvent = do
                --eb <- eventBoxNew
                --set eb [ containerChild := hb ]
                --boxPackStart ext_box eb PackGrow 0
                boxPackStart ext_box hb PackGrow 0
                hb `on` buttonReleaseEvent $ do
                    -- movemos el proofFocus hasta donde está esta expresión.
                    eventWithState (updateModifExpr fUpdate >>
                                    updateSelectedExpr fGet) proofRef
                    --liftIO $ widgetShowAll eb
                    liftIO $ widgetShowAll hb
                    return False
                    
                (choicesButton w) `on` buttonPressEvent $ tryEvent $
                            eventWithState (changeProofFocus' >>
                                            showChoices) proofRef
--                 eb `on` buttonPressEvent $ do
--                     LeftButton <- eventButton
--                     liftIO $ debug "funcking evento"
--                     eventWithState changeProofFocus' proofRef
--                     liftIO $ widgetShowAll eb
--                     return False

        changeProofFocus' = unSelectBox >>
                            changeProofFocus moveFocus Nothing >>
                            getProof >>= \(p,path) ->
                            selectBox (p,path) focusBg top_box >>
                            liftIO (proofFocusToBox path top_box) >>= \center_box ->
                            liftIO (axiomBoxFromCenterBox center_box) >>= \axiom_box ->
                            changeProofFocus moveFocus (Just axiom_box)
                        
        showChoices = do
            menu <- liftIO menuNew
            pf <- getProof
            exp1 <- return (fromJust $ getStartFocus pf)
            m_axiom <- return (getBasicFocus pf)
            case m_axiom of
                Nothing -> return ()
                Just axiom -> do
                    choices <- return (possibleExpr (toExpr exp1) axiom)
                    addToMenu menu choices
                    liftIO $ widgetShowAll menu
                    liftIO $ menuPopup menu Nothing
            
        addToMenu m = mapM_ addItem
            where addItem e = do
                                item <- liftIO $ menuItemNewWithLabel (show e)
                                liftIO $ menuShellAppend m item
                                ref <- get
                                liftIO (item `on` buttonPressEvent $ tryEvent $
                                        flip eventWithState ref $ 
                                            -- Actualizamos la expresion
                                            updateModifExpr fUpdate >>
                                            updateSelectedExpr fGet >>
                                            writeExprWidget e (formBox w) >>
                                            updateExpr e)

        setupOptionExprWidget :: Window -> PreExpr-> IState ()
        setupOptionExprWidget win e = do
            bAnot <- makeOptionEvent win "✐" Nothing
            
            bT <- makeOptionEvent win "⑂" (Just $ getProof >>= \pf -> return $ fGet pf)
            
            bInfo <- makeLayoutTypeCheckStatus
            
            liftIO (boxPackStart ext_box bAnot PackNatural 10 >>
                    boxPackStart ext_box bT PackNatural 10 >>
                    boxPackStart ext_box bInfo PackNatural 10 >>
                    widgetShowAll ext_box)

        makeLayoutTypeCheckStatus :: IState Fixed
        makeLayoutTypeCheckStatus = liftIO $ 
            do
            l <- layoutNew Nothing Nothing
            set l [widgetWidthRequest := 25, widgetHeightRequest := 25]
            widgetModifyBg l (toEnum 0) whiteBg
            f <- fixedNew
            fixedPut f l (0,12)
            return f
        

{- | Funcion para obtener la caja correspondiente al paso de la prueba en el que estamos
   dentro de una transitividad.
    El parámetro "box" debe ser una caja construida con "createCenterBox". Cada una de esas
    cajas tendrá 3 hijos. El primero corresponde a la central box de la subprueba izquierda,
    El segundo es una expresion y el tercero será la central box que corresponde a la subprueba
    derecha.
    -}
proofFocusToBox :: ProofPath -> VBox -> IO VBox
proofFocusToBox = go
    where go p b = debug ("proofFocusToBox: Path = " ++ show p) >>
                   case p of
                        Top -> return b
                        TransL p' _ -> go p' b >>= getBox 0
                        TransR _ p' -> go p' b >>= getBox 2
                     
          getBox i b  = containerGetChildren b >>= \ chd ->
                       if length chd <= i
                       then error ("La lista tiene " ++ show (length chd)
                                         ++ " elementos, pero se esperan al menos "
                                         ++  show (i+1) ++ " elementos.")
                       else let b' = chd!!i in
                            if isVBox b'
                            then return $ castToVBox b'
                            else error $ "No es un VBox (index: " ++
                                          show i ++")"
                     
{- | Funcion que obtiene la caja de axioma desde una caja creada por "createCenterBox"
     PRE: center_box tiene la estructura que se crea en "createCenterBox", con un solo hijo
          que contiene el comboBox de relación, la caja de axioma.
          La prueba a la que corresponde la center_box debe encontrarse en una hoja del arbol
          del zipper de la prueba general.
     -}
axiomBoxFromCenterBox :: VBox -> IO HBox
axiomBoxFromCenterBox center_box = containerGetChildren center_box >>= \chd ->
                            if length chd /= 1
                            then error "axiomBoxFromCenterBox: La caja no tiene exactamente un hijo"
                            else let b = chd!!0 in
                                containerGetChildren (castToContainer b) >>= \chd' ->
                                if length chd' /= 3
                                then error "axiomBoxFromCenterBox: El hijo del center_box no tiene 3 hijos"
                                else let ev_box = chd'!!1 in
                                    containerGetChildren (castToContainer ev_box) >>= \chd'' ->
                                    if length chd'' /= 1
                                    then error "axiomBoxFromCenterBox: El event_box no tiene un solo hijo"
                                    else let axiom_box = chd''!!0 in
                                        if isHBox axiom_box
                                        then return $ castToHBox axiom_box
                                        else error $ "axiomBoxFromCenterBox: El axiom_box no es HBox"
                                
                                          
