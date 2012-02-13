-- | Modulo de muestra y control de eventos sobre pruebas.
module Equ.GUI.Proof where

import Equ.GUI.Types hiding (GState)
import Equ.GUI.State hiding (getExprWidget)
import Equ.GUI.State.Expr
import Equ.GUI.Utils

import Equ.GUI.Settings
import Equ.GUI.TruthList
import Equ.Rule
import Equ.Theories
import Equ.Proof
import qualified Equ.Proof.Proof as P(getStart,getEnd,getBasic,getRel,getCtx)
import Equ.Proof.ListedProof
import Equ.PreExpr hiding (goDownL,goDownR,goRight,goUp,goTop)
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

import System.Glib.GObject(toGObject)

-- | Crea una nueva referencia
newProofState :: (Maybe Proof) -> HBox -> ExprWidget -> ExprWidget ->
                 ProofStepWidget -> IState ProofState
newProofState (Just p) axiom_box expr1W expr2W proofW= return pr
    where
        pr :: ProofState
        pr = ProofState { proof = fromJust $ createListedProof (toProofFocus p)
                        , validProof = validateProof p
                        , proofWidget = fromJust $ createListedProof (pw,Top)
                        }
                        
        pw = Simple () () expr1W expr2W proofW
            
            
newProofState Nothing axiom_box expr1W expr2W proofW = getGlobalCtx >>=
                                  return . pr . Just
    where
        pr :: Maybe Ctx -> ProofState
        pr c = ProofState { proof = fromJust $ createListedProof $ p c
                          , validProof = validateProof $ toProof (p c)
                          , proofWidget = fromJust $ createListedProof (pw,Top)
                        }
        p c = emptyProof c $ head $ relationList
        
        pw = Simple () () expr1W expr2W proofW
                        
                        
-- | Carga una prueba a la interfaz. 
loadProof :: Proof -> VBox -> VBox -> ExprWidget -> ProofStepWidget -> IState ()
loadProof p ret_box truthBox initExprWidget proofStepW = do
    
    --newExpr_w  <- newExprWidget (toExpr $ fromRight $ getEnd p) (ProofMove moveToEnd) truthBox
    newExpr_w  <- newExprWidget (toExpr $ fromRight $ getEnd p) 0
    
    empty_box1 <- io $ hBoxNew False 2
    proof <- newProofState (Just p) empty_box1 initExprWidget newExpr_w proofStepW
    updateProofState proof
    
    -- Expresión inicial:
    removeAllChildren (formBox initExprWidget)
    initExpr <- return . fromRight $ getStart p
    
    labelInitExpr <- io $ labelNew (Just $ show $ toExpr initExpr)
    io $ boxPackStart (formBox initExprWidget) labelInitExpr PackNatural 2
    io $ widgetShowAll (formBox initExprWidget)
    
    io (--boxPackStart ret_box hboxInit PackNatural 2 >>
        boxPackStart ret_box truthBox PackNatural 2 >>
        boxPackStart ret_box (extBox newExpr_w) PackNatural 2)
    
    completeProof p truthBox 0
    
    
completeProof :: Proof -> VBox -> Int -> IState ()
completeProof p@(Trans _ rel f1 fm f2 p1 p2) center_box ind = do
    (boxL,boxR) <- newStepProof (toExpr fm) ind center_box
    
    completeProof p1 boxL ind
    completeProof p2 boxR (ind+1)

completeProof (Hole _ rel f1 f2) center_box ind =
    --addStepProof center_box top_box moveFocus Nothing >>
    return ()

completeProof p@(Simple _ rel f1 f2 b) center_box ind =
    --addStepProof center_box top_box moveFocus (Just b) >>
    changeProofFocusAndShow ind >>
    getProofWidget >>= \lpw ->
    writeTruth b (axiomWidget $ fromJust $ getSelBasic lpw) >>
    return ()

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
    
    labelInitExpr <- io $ labelNew (Just $ show $ toExpr initExpr)
    io $ boxPackStart (formBox initExprWidget) labelInitExpr PackNatural 2
    io $ widgetShowAll (formBox initExprWidget)
    
    -- truthBox es la caja central para colocar la relacion y el axioma aplicado. La
    -- funcion para mover el foco es ir hasta el tope.
    io $ debug $ "Antes de crear el widget de paso de prueba"
    
    firstStepProof <- addStepProof truthBox 0 Nothing
    
    io $ debug $ "Pude crear el widget de paso de prueba"
        
    maybe (emptyProof truthBox initExprWidget firstStepProof) 
          (\p -> loadProof p ret_box truthBox initExprWidget firstStepProof) proof
    
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

    where emptyProof box initExprW firstStepW = do
            --hboxInit <- createExprWidget holePreExpr goTopbox
            expr_w  <- newExprWidget holePreExpr 0

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
                                        reportErrWithErrPaned (show errorProof))
--                                         return (getMoveFocus errorProof) >>= \move ->
--                                             changeProofFocus move move Nothing >>
--                                             selectBox errBg)
                                       

-- | Creación de línea de justificación de paso en una prueba.
addStepProof :: VBox -> Int -> Maybe Basic -> IState ProofStepWidget
addStepProof center_box stepIndex maybe_basic = do
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
        
    io $ boxPackStart center_box hbox PackNatural 5
    
    flip F.mapM_ maybe_basic $ flip writeTruth axiom_box
    
    psw <- return ProofStepWidget {
                    relation = (combo_rel,store_rel) 
                  , axiomWidget = axiom_box 
                  , addStepButton = addStepProofButton
                  , eventBoxAxiom = eb_axiom_box
                  , validImage = imageValidStep
                  , stepBox = hbox
                  , centerBox = center_box
                  , stepEventsIds = []
    }
    
    psw' <- eventsProofStep psw stepIndex
    
    return psw'                 
      
unSelectBox :: IRG      
unSelectBox = getStepProofBox >>=
              F.mapM_ (\box -> unlightBox box (Just axiomBg))
              
              
--             io (widgetGetParent axiom_box) >>= \ eb_box ->
--             F.forM_ eb_box 
--                         (\ p -> io (widgetGetParent p) >>=
--                         flip unlightBox (Just axiomBg) . castToHBox . fromJust
--                         )

selectBox :: Color -> IRG
selectBox color = 
            getStepProofBox >>=
            F.mapM_ (\box -> highlightBox box color)
           
               
--             io (debug "Probando zipper de widgets") >>
--             getProofWidget >>= \(pw,pathW) ->
--             io (debug $ "Path en el proofFocusWidget es: " ++ show pathW) >>
--             io (widgetGetParent box) >>= \center_box ->
--             F.forM_ center_box 
--                 (\b -> getProof >>= \(_,path) ->
--                 io (proofFocusToBox path top_box) >>= \b' ->
--                 if (castToVBox b)==(castToVBox b') then io (debug ("proofFocusToBox da la misma caja que el zipper"))
--                                                    else io (debug ("proofFocusToBox NO da la misma caja que el zipper"))
--                 )
--             
--             io (widgetGetParent axiom_box) >>= \ eb_box ->
--             F.forM_ eb_box 
--                         (\ p -> io (widgetGetParent p) >>= \box ->
--                         highlightBox (castToHBox $ fromJust $ box) color
--                         )
                                 
newStepProof :: PreExpr -> Int -> VBox -> IState (VBox,VBox)
newStepProof expr stepIndex container = do
    removeAllChildren container
    -- Movemos el ProofFocus hasta donde está el hueco que queremos reemplazar
    -- por una transitividad
    
    
    changeProofFocusAndShow stepIndex
        -- Reemplazamos el hueco por una transitividad
    
    
    lp <- getProof
    lpw <- getProofWidget
    
    updateProof (addStepOnPosition stepIndex fProof (\e i -> e) (\p i -> p) lp) 
    
    relation <- getRelPF
    
    centerBoxL <- io $vBoxNew False 2
    newStepWL <- addStepProof centerBoxL stepIndex Nothing
    centerBoxR <- io $ vBoxNew False 2
    newStepWR <- addStepProof centerBoxR (stepIndex + 1) Nothing
    expr_w <- newExprWidget expr stepIndex
    
    io (boxPackStart container centerBoxL PackNatural 5 >>
            boxPackStart container (extBox expr_w) PackNatural 5 >>
            boxPackStart container centerBoxR PackNatural 5 >>
        
            widgetShowAll container)
    
    lpw' <- addStepOnPositionM stepIndex (fProofWidget expr_w newStepWL newStepWR)
                                    resetSignalsExpr resetSignalsProofStep lpw
    
    updateProofWidget lpw'

    return (centerBoxL,centerBoxR)
    
    {- Cuando se modifique la expresion que queda en el medio de esta transitividad,
       tenemos que actualizar la expr del medio de la transitividad, la expr final de la
       prueba izquierda y la expr inicial de la prueba derecha. Para hacer todo esto vamos moviéndonos
       con el zipper
       -}
       where 
            fProof :: Proof -> (Focus,Proof,Proof)
            fProof proof = let (ctx,rel,f1,f2) = (fromJust $ P.getCtx proof,
                                               fromJust $ P.getRel proof,
                                               fromJust $ P.getStart proof,
                                               fromJust $ P.getEnd proof) in
                                (emptyExpr,(Hole ctx rel f1 emptyExpr),
                                    (Hole ctx rel emptyExpr f2))
                
            fProofWidget :: ExprWidget -> ProofStepWidget -> ProofStepWidget ->
                            ProofWidget -> (ExprWidget,ProofWidget,ProofWidget)
            fProofWidget expr_w newStepWL newStepWR p = 
                  (expr_w,Simple () () (fromJust $ P.getStart p) expr_w newStepWL,
                            Simple () () expr_w (fromJust $ P.getEnd p) newStepWR)
            
relationListStore :: IO (ListStore Relation)
relationListStore = listStoreNew relationList 

newComboRel :: Relation -> IO (ComboBox,ListStore Relation)
newComboRel rel = do
    list <- relationListStore
    combo <- comboBoxNew
    renderer <- cellRendererTextNew
    cellLayoutPackStart combo renderer False
    cellLayoutSetAttributes combo renderer list 
                  (\ind -> [cellText := unpack $ relRepr ind])
    comboBoxSetModel combo (Just list)
    selectRelation rel combo list
    return (combo,list)
            
selectRelation :: Relation -> ComboBox -> ListStore Relation -> IO ()
selectRelation r combo lstore = do
    ls <- listStoreToList lstore
    comboBoxSetActive combo (getIndexFromList ls r)
    
    where getIndexFromList ls rel = fromJust $ elemIndex rel ls
            
newExprWidget :: PreExpr -> Int -> IState ExprWidget              
newExprWidget expr stepIndex = do

    exprWidget <- createExprWidget False
   
    eventsExprWidget exprWidget stepIndex
    flip runReaderT (exprWidget,id,stepIndex) (writeExprWidget (formBox exprWidget) expr) 
    
    return exprWidget
    
-- | Setea los eventos de un widget de expresion. La funcion f es la
-- que se utiliza para actualizar la expresion dentro de la prueba
eventsExprWidget :: ExprWidget -> Int -> IState ExprWidget
eventsExprWidget exprWidget stepIndex = do
    s <- get 
    win <- getWindow
    runReaderT (setupOptionExprWidget win >>
                setupForm (formBox exprWidget) Editable) (exprWidget,id,stepIndex)
    (ConnectId o1,ConnectId o2) <- io (setupFocusEvent s)
    return $ exprWidget {exprEventsIds = [ConnectId (toGObject o1),ConnectId (toGObject o2)]}
    
    where hb = extBox exprWidget
          setupFocusEvent :: GRef -> IO (ConnectId HBox,ConnectId Button)
          setupFocusEvent s = do
            let Just choices = choicesButton exprWidget
            cid1 <- hb `on` buttonReleaseEvent $ do
                    flip eventWithState s $
                    -- movemos el proofFocus hasta donde está esta expresión.
                         updateExprWidget exprWidget  >>
                         changeProofFocus'
                    io (widgetShowAll hb)
                    return True
                    
            cid2 <- choices `on` buttonPressEvent $ tryEvent $
                        eventWithState (changeProofFocus' >> showChoices) s
            return (cid1,cid2)

          changeProofFocus' = changeProofFocusAndShow stepIndex >>
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
                    item <- io $ menuItemNewWithLabel $ show e
                    io $ menuShellAppend m item
                    s' <- get
                    io $ item `on` buttonPressEvent $ tryEvent $
                             flip eventWithState s' $ 
                                  -- Actualizamos la expresion
                                  changeProofFocus' >>
                                  updateExprWidget exprWidget >>
                                  runReaderT (writeExprWidget (formBox exprWidget) e) (exprWidget, id,stepIndex) >>
                                  updateExpr e id

resetSignalsExpr :: ExprWidget -> Int -> IState ExprWidget
resetSignalsExpr ew newInd = let ls = exprEventsIds ew in do
                                io $ mapM_ signalDisconnect ls
                                ew' <- eventsExprWidget ew newInd
                                return ew'
                                  
eventsProofStep :: ProofStepWidget -> Int -> IState ProofStepWidget
eventsProofStep psw ind = do
    s <- get
    combo_rel <- return (fst $ relation psw)
    store_rel <- return (snd $ relation psw)
    eb_axiom_box <- return (eventBoxAxiom psw)
    axiom_box <- return (axiomWidget psw)
    
    cid1 <- addHandler eb_axiom_box buttonPressEvent (do
        LeftButton <- eventButton
        io $ debug "axiom_box clicked"
        eventWithState (changeProofFocusAndShow ind) s)
        
        
    cid2 <- addHandler eb_axiom_box  buttonPressEvent (do
        RightButton <- eventButton
        io $ debug "axiom_box right clicked"
        eventWithState (changeProofFocusAndShow ind >>
                        removeAllChildren axiom_box) s

        label <- io (labelNew (Just $ emptyLabel))
        io $ boxPackStart axiom_box label PackGrow 0
        eventWithState (getProof >>= updateProof . toHoleProof) s
        io $ widgetShowAll axiom_box)
        
    cid3 <- io $ (addStepButton psw) `on` buttonPressEvent $ 
       flip eventWithState s (newStepProof holePreExpr ind (centerBox psw)) >>
       return False
       
    cid4 <- io (combo_rel `on` changed $ evalStateT (changeItem combo_rel store_rel ind) s)
       
    return psw { eventsProofStep = [cid1,cid2,cid3,cid4] }
       
    where changeItem c list ind= do 
            changeProofFocusAndShow ind
            ind <- io $ comboBoxGetActive c
            newRel <- io $ listStoreGetValue list ind
            updateRelation newRel
            validateStep
        
resetSignalsProofStep :: ProofStepWidget -> Int -> IState ProofStepWidget
resetSignalsProofStep psw ind = let ls = stepEventsIds psw in do
                                io $ mapM_ signalDisconnect ls
                                psw' <- eventsProofStep psw ind
                                return psw'
                                  

-- | Descarta la prueba actual.
discardProof centralBox expr_w = unsetProofState >>
                                  removeAllChildren centralBox >>
                                  getExpr >>= \e ->
                                  runReaderT (reloadExpr (toExpr e)) (expr_w,id,ProofMove Just)


                                        
changeProofFocusAndShow moveFocus moveFocusW box = 
                                 unSelectBox >>
                                 changeProofFocus moveFocus moveFocusW box >>
                                 selectBox focusBg

                                  
-- LAS SIGUIENTES FUNCIONES NO SE USAN MAS.
                                  
                                  
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

                                        
                                        