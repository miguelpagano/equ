-- | Modulo de muestra y control de eventos sobre pruebas.
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
import Equ.GUI.Expr (clearFocus,writeExprWidget,setupForm
                    , makeOptionEvent, configAnnotTB, configTypeTreeTB
                    , newExprState, reloadExpr)
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
import Control.Applicative((<$>))
import qualified Data.Foldable as F (forM_,mapM_)

-- | Crea una nueva referencia
newProofState :: (Maybe Proof) -> HBox -> IState ProofState
newProofState (Just p) axiom_box = return pr
    where
        pr :: ProofState
        pr = ProofState { proof = toProofFocus p
                        , validProof = validateProof p
                        , axiomBox = axiom_box
                        }
newProofState Nothing axiom_box = getGlobalCtx >>=
                                  return . pr . Just
    where
        pr :: Maybe Ctx -> ProofState
        pr c = ProofState { proof = p c
                          , validProof = validateProof $ toProof (p c)
                          , axiomBox = axiom_box
                        }
        p c = emptyProof c $ head $ relationList
                        
                        
-- | Carga una prueba a la interfaz. 
loadProof :: Proof -> VBox -> VBox -> HBox -> IState ()
loadProof p ret_box truthBox initExprBox = do
    
    empty_box1 <- io $ hBoxNew False 2
    proof <- newProofState (Just p) empty_box1
    updateProofState proof
    
    --hboxInit <- createExprWidget (toExpr $ fromRight $ getStart p) goTop updateFirstExpr getFirstExpr truthBox
    
    -- Expresión inicial:
    removeAllChildren initExprBox
    initExpr <- return . fromRight $ getStart p
    
    labelInitExpr <- io $ labelNew (Just $ show $ toExpr initExpr)
    io $ boxPackStart initExprBox labelInitExpr PackNatural 2
    io $ widgetShowAll initExprBox
    
    hboxEnd  <- createExprWidget (toExpr $ fromRight $ getEnd p) moveToEnd truthBox
    
    io (--boxPackStart ret_box hboxInit PackNatural 2 >>
        boxPackStart ret_box truthBox PackNatural 2 >>
        boxPackStart ret_box hboxEnd PackNatural 2)
    
    completeProof p truthBox truthBox goTop
    
    
completeProof :: Proof -> VBox -> VBox -> (ProofFocus -> Maybe ProofFocus) -> IState ()
completeProof p@(Trans _ rel f1 fm f2 p1 p2) center_box top_box moveFocus = do
    (boxL,boxR) <- newStepProof (toExpr fm) moveFocus center_box top_box
    
    completeProof p1 boxL top_box (goDownL . fromJust . moveFocus)
    completeProof p2 boxR top_box  (goDownR . fromJust . moveFocus)  

completeProof (Hole _ rel f1 f2) center_box top_box  moveFocus =
    addStepProof center_box top_box moveFocus Nothing

completeProof p@(Simple _ rel f1 f2 b) center_box top_box moveFocus =
    addStepProof center_box top_box moveFocus (Just b)

-- | Crea toda la estructura necesaria para una nueva prueba.  Si el
-- primer argumento es @Nothing@, entonces se crea la estructura para
-- una prueba vacía; si es @Just p@, entonces se crea para la prueba @p@.
createNewProof :: (Maybe Proof) -> VBox -> VBox -> HBox -> IState ()
createNewProof proof ret_box truthBox initExprBox = do
    io $ debug "creando prueba..."
    
    -- delete all children
    removeAllChildren ret_box
    
    removeAllChildren initExprBox
    initExpr <- getExpr
    
    labelInitExpr <- io $ labelNew (Just $ show $ toExpr initExpr)
    io $ boxPackStart initExprBox labelInitExpr PackNatural 2
    io $ widgetShowAll initExprBox
    
    initState

    -- truthBox es la caja central para colocar la relacion y el axioma aplicado. La
    -- funcion para mover el foco es ir hasta el tope.
    addStepProof truthBox truthBox goTop  Nothing
    
    maybe (emptyProof truthBox) (\p -> loadProof p ret_box truthBox initExprBox) proof
    
--     valid_button <- io $ buttonNewWithLabel "Validar prueba"
--     validImage <- io $ imageNewFromStock stockCancel IconSizeSmallToolbar
--     validProofHBox <- io $ hBoxNew False 2
--     io (boxPackStart validProofHBox valid_button PackGrow 5 >>
--         boxPackStart validProofHBox validImage PackNatural 5 >>
--         boxPackStart ret_box validProofHBox PackNatural 20
--        )

    s <- get    
--     io $ (valid_button `on` buttonPressEvent $ tryEvent $
--                             eventWithState (checkProof validImage truthBox) s)
    io $ widgetShowAll ret_box

    where emptyProof box = do
            --hboxInit <- createExprWidget holePreExpr goTopbox
            hboxEnd  <- createExprWidget holePreExpr moveToEnd box

            io (--boxPackStart ret_box hboxInit PackNatural 2 >>
                boxPackStart ret_box box PackNatural 2 >>
                boxPackStart ret_box hboxEnd PackNatural 2
               )


initState :: IRG
initState = do
    -- TODO: Ver si está bien poner cajas vacias para la caja de expresion y la de 
    -- axiomas al iniciar la referencia. Si el usuario elige un símbolo para construir 
    -- expresión o elige un axioma ANTES de hacer click en alguna caja, entonces la prueba
    -- se actualiza en el estado pero no se muestra en la interfaz (ya que esas cajas vacías
    -- nunca fueron agregadas a la interfaz)
    
    -- inicialmente ponemos una caja vacia en el foco, asumiendo que no hay ninguna
    -- expresión enfocada.
    empty_box1 <- io $ hBoxNew False 2
    initExpr <- getExpr
    proof' <- newProofState (Just $ pr initExpr) empty_box1
    updateProofState proof'
    
--     hbox1 <- io $ hBoxNew False 2
--     hbox2 <- io $ hBoxNew False 2
--     expr' <- newExprState emptyExpr hbox1 hbox2
--     updateExprState expr'    
    
    where pr e= flip newProofWithStart e $ head $ relationList
    
-- TODO: VER DONDE METER ESTAS FUNCIONES
-- TODO: Comprobar que el cambio no afecta la semántica.
updateFirstExpr pf f = goTop pf >>= flip updateStartFocus f
updateFinalExpr pf f = goTop pf >>= flip updateEndFocus f

-- TODO: Hacer que estas funciones devuelvan Maybes y manejar
-- apropiadamente los casos Nothing en los lugares que se usan.
getFirstExpr = fromJust . getStartFocus . fromJust . goTop
getFinalExpr = fromJust . getEndFocus . fromJust . goTop

checkProof :: Image -> VBox -> IState ()
checkProof validImage top_box = getProofState >>= (F.mapM_ $ \ps ->
                                updateValidProof >> checkValidProof >>= \valid ->
                                if valid 
                                then updateImageValid iconValidProof
                                else getValidProof >>= \(Left errorProof) ->
                                      io (putStrLn (show errorProof)) >>
                                       updateImageValid iconErrorProof >>
                                       reportErrWithErrPaned (show errorProof) >>
                                       unSelectBox >>
                                       getProof >>= \pf ->
                                       return ((getMoveFocus errorProof) (goTop' pf)) >>=
                                       \pf -> selectBox pf errBg top_box)
                                       

-- | Creación de línea de justificación de paso en una prueba.
addStepProof :: VBox -> VBox -> (ProofFocus -> Maybe ProofFocus) -> 
                   Maybe Basic -> IState ()
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
    addStepProofButton <- io $ makeButtonWithImage stockGoDown
    
    io $ setToolTip addStepProofButton "Agregar Paso"
    io $ widgetSetSizeRequest button_box 200 (-1)
    
    eb_axiom_box <- io $ eventBoxNew 

    io (widgetSetSizeRequest combo_rel 80 (-1) >>
            boxPackStart button_box addStepProofButton PackNatural 2 >>
            boxPackStart hbox combo_rel PackNatural 5 >>
            set eb_axiom_box [ containerChild := axiom_box ] >>
            boxPackStart hbox eb_axiom_box PackGrow 5 >> 
            boxPackStart hbox button_box PackNatural 1 >>
            highlightBox hbox axiomBg)

    s <- get
    io (combo_rel `on` changed $ evalStateT (changeItem combo_rel store_rel axiom_box) s)

    addHandler eb_axiom_box buttonPressEvent (do
        LeftButton <- eventButton
        io $ debug "axiom_box clicked"
        eventWithState (unSelectBox >>
                        changeProofFocus moveFocus (Just axiom_box) >>
                        getProof >>= \pf ->
                        selectBox pf focusBg top_box
                        ) s)
        
        
    addHandler eb_axiom_box  buttonPressEvent (do
        RightButton <- eventButton
        io $ debug "axiom_box right clicked"
        eventWithState (changeProofFocus moveFocus (Just axiom_box) >>
                        removeAllChildren axiom_box) s

        label <- io (labelNew (Just $ emptyLabel))
        io $ boxPackStart axiom_box label PackGrow 0
        eventWithState (getProof >>= updateProof . toHoleProof) s
        io $ widgetShowAll axiom_box)
        
    io $ addStepProofButton `on` buttonPressEvent $ 
       flip eventWithState s (newStepProof holePreExpr moveFocus center_box top_box) >>
       return False
        
        
    io $ boxPackStart center_box hbox PackNatural 5
    
    flip F.mapM_ maybe_basic $ flip writeTruth axiom_box
            
    where changeItem c list box = do 
            unSelectBox
            changeProofFocus moveFocus (Just box)
            pf <- getProof
            selectBox pf focusBg top_box
            ind <- io $ comboBoxGetActive c
            newRel <- io $ listStoreGetValue list ind
            updateRelation newRel
      
unSelectBox :: IRG      
unSelectBox = getAxiomBox >>= \ axiom_box ->
            io (widgetGetParent axiom_box) >>= \ eb_box ->
            F.forM_ eb_box 
                        (\ p -> io (widgetGetParent p) >>=
                        flip unlightBox (Just axiomBg) . castToHBox . fromJust
                        )

selectBox :: ProofFocus -> Color -> VBox -> IRG
selectBox (_,path) color top_box = io (proofFocusToBox path top_box) >>= \cbox ->
            io (containerGetChildren cbox) >>= \chd ->
                highlightBox (castToHBox $ chd!!0) color
                                 
newStepProof :: PreExpr -> (ProofFocus -> Maybe ProofFocus) ->
                VBox -> VBox -> IState (VBox,VBox)
newStepProof expr moveFocus container top_box = do
    removeAllChildren container
    -- Movemos el ProofFocus hasta donde está el hueco que queremos reemplazar
    -- por una transitividad
    changeProofFocus moveFocus Nothing 
        -- Reemplazamos el hueco por una transitividad
    pf <- getProof
    updateProof (addEmptyStep pf) 
    -- Dejamos enfocada la prueba derecha de la transitividad
    changeProofFocus goDownR Nothing
    
    relation <- getRelPF
    
    centerBoxL <- io $vBoxNew False 2
    addStepProof centerBoxL top_box (goDownL . fromJust . moveFocus) Nothing
    centerBoxR <- io $ vBoxNew False 2
    addStepProof centerBoxR top_box (goDownR . fromJust . moveFocus) Nothing
    exprBox <- createExprWidget expr moveFocus' top_box
    
    io (boxPackStart container centerBoxL PackNatural 5 >>
            boxPackStart container exprBox PackNatural 5 >>
            boxPackStart container centerBoxR PackNatural 5 >>
        
            widgetShowAll container)
    
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
            
createExprWidget :: PreExpr -> (ProofFocus -> Maybe ProofFocus) ->
                    VBox -> IState HBox
              
createExprWidget expr moveFocus top_box = do
  
    hbox    <- io $ hBoxNew False 2
    boxExprWidget <- io $ hBoxNew False 2
    
    box <- io $ hBoxNew False 2
    expr_choices <- io $ makeButtonWithImage stockIndex
    io $ setToolTip expr_choices "Expresiones posibles"
    button_box <- io $ hButtonBoxNew
    io (widgetSetSizeRequest button_box 200 (-1) >>
        widgetSetSizeRequest hbox (-1) 50 >>

        boxPackStart button_box expr_choices PackNatural 2 >>
        boxPackStart boxExprWidget box PackGrow 1 >>
        boxPackStart boxExprWidget button_box PackNatural 1    
       )
    
    exprWidget <- return $ ExprWidget { extBox = boxExprWidget -- Box externa
                                     , formBox = box
                                     , choicesButton = Just expr_choices
                                     }
    
    eventsExprWidget expr hbox exprWidget moveFocus top_box
    
    writeExprWidget expr box
    
    return hbox
    
-- | Setea los eventos de un widget de expresion. La funcion f es la
-- que se utiliza para actualizar la expresion dentro de la prueba
eventsExprWidget :: PreExpr -> HBox -> ExprWidget -> 
                    (ProofFocus -> Maybe ProofFocus) ->
                    VBox -> IState ToggleButton
eventsExprWidget expr ext_box w moveFocus top_box =
    let fGet = getEndFocus . fromJust . moveFocus in
    get >>= \s ->
    getWindow >>= \win ->
    setupOptionExprWidget win expr >>= \tbT ->
    io (setupFocusEvent s tbT) >>
    updatePath (id,id) >>
    setupForm (formBox w) Editable >>
    return tbT
    
    where hb = extBox w
          setupFocusEvent :: GRef -> ToggleButton -> IO (ConnectId Button)
          setupFocusEvent s tbT = do
                boxPackStart ext_box hb PackGrow 0
                hb `on` buttonPressEvent $ do
                    -- movemos el proofFocus hasta donde está esta expresión.
                    eventWithState (updateExprWidget w >>
                                    changeProofFocus' >>
                                    io (set tbT [toggleButtonActive := False])) s
                    io $ widgetShowAll hb
                    return True
                    
                (fromJust $ choicesButton w) `on` buttonPressEvent $ tryEvent $
                            eventWithState (changeProofFocus' >>
                                            showChoices) s

          changeProofFocus' = unSelectBox >>
                              changeProofFocus moveFocus Nothing >>
                              getProof >>= \(p,path) ->
                              selectBox (p,path) focusBg top_box >>
                              io (proofFocusToBox path top_box) >>= \center_box ->
                              io (axiomBoxFromCenterBox center_box) >>= \axiom_box ->
                              changeProofFocus moveFocus (Just axiom_box) >>
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
                    item <- io $ menuItemNewWithLabel (show e)
                    io $ menuShellAppend m item
                    ref <- get
                    io (item `on` buttonPressEvent $ tryEvent $
                                        flip eventWithState ref $ 
                                            -- Actualizamos la expresion
                                            changeProofFocus' >>
                                            updateExprWidget w >>
                                            writeExprWidget e (formBox w) >>
                                            updateExpr e)

          setupOptionExprWidget :: Window -> PreExpr-> IState ToggleButton
          setupOptionExprWidget win e = do

            exprButtons <- io hButtonBoxNew

            bAnot <- makeOptionEvent win stockEdit (configAnnotTB putStrLn)
            io $ setToolTip bAnot "Anotaciones"
            
            bT    <- makeOptionEvent win stockIndex 
                                (configTypeTreeTB (getSelectedExpr) 
                                (\(e,_) -> updateExpr e) w)
            io $ setToolTip bT "Árbol de tipado"
            
            bInfo <- makeLayoutTypeCheckStatus
            
            io (containerAdd exprButtons bAnot  >>
                containerAdd exprButtons bT >>
                containerAdd exprButtons bInfo >>
                boxPackStart ext_box exprButtons PackNatural 10 >>
                widgetShowAll ext_box)
            return bT

          makeLayoutTypeCheckStatus :: IState Image
          makeLayoutTypeCheckStatus = io $ imageNewFromStock stockInfo IconSizeMenu
        


-- | Descarta la prueba actual.
discardProof centralBox formBox = unsetProofState >>
                                  removeAllChildren centralBox >>
                                  getExpr >>= \e ->
                                  reloadExpr formBox (toExpr e)


{- | Funcion para obtener la caja correspondiente al paso de la prueba en el que estamos
   dentro de una transitividad.
    El parámetro "box" debe ser una caja construida con "addStepProof". Cada una de esas
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
                     
{- | Funcion que obtiene la caja de axioma desde una caja creada por "addStepProof"
     PRE: center_box tiene la estructura que se crea en "addStepProof", con un solo hijo
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

