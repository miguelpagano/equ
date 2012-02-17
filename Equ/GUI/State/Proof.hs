{-# Language OverloadedStrings #-}
-- | Utilidades varias que tienen que ver con el estado de la
-- interfaz (es probable que se muden a Equ.GUI.State) y con
-- funciones convenientes que podrían mudarse a otros módulos.
module Equ.GUI.State.Proof
    where

import Equ.GUI.Types
import Equ.GUI.State.Internal hiding (local)
import Equ.GUI.Utils

import Equ.Rule (Relation, relEq)

import Equ.Proof.Proof
import Equ.Proof.Error(errEmptyProof)
import Equ.Proof(ProofFocus,ProofFocus',updateStartFocus,updateEndFocus,PM,validateProof,
                 toProof,goFirstLeft,updateMiddleFocus,goUp',getEndFocus,goRight,goEnd,goDownL',
                  getBasicFocus, validateProofFocus, goNextStep, goPrevStep)


import Graphics.UI.Gtk (HBox,StockId,imageSetFromStock,IconSize(IconSizeSmallToolbar))
import Data.Maybe (fromJust)
import qualified Data.Foldable as F

import Control.Arrow(first,(&&&))

getProofState :: IState (Maybe ProofState)
getProofState = getStatePartDbg "getProofState" gProof

getProof :: IState ProofFocus
getProof = getStatePartDbg "getProof" (proof . fromJust . gProof)

getProofWidget :: IState ProofFocusWidget
getProofWidget = getStatePartDbg "getProofWidget" (proofWidget . fromJust . gProof)


getValidProof :: IState (PM Proof)
getValidProof = getStatePart (maybe (Left errEmptyProof) validProof . gProof)

updateImageValid :: StockId -> IRG
updateImageValid icon = getStatePart imageValid >>= \validImage ->
                        io (imageSetFromStock validImage icon IconSizeSmallToolbar)
                    

restoreValidProofImage :: IRG
restoreValidProofImage = updateImageValid iconUnknownProof

-- Las siguientes funciones validan el paso en el que la prueba está enfocada.
validateStep :: IState ()
validateStep = getProofState >>= 
               F.mapM_ (\ps -> getProof >>= \pf ->
               case validateProofFocus pf of
                    Left _ -> updateStepWidgetImage iconErrorProof
                    Right _ -> updateStepWidgetImage iconValidProof
                   )
                   
updateStepWidgetImage :: StockId -> IState ()
updateStepWidgetImage icon = getProofState >>= 
                        F.mapM_ (\ps -> getProofWidget >>= \pfw ->
                        let image = validImage (fromJust $ getBasicFocus pfw) in
                             io (imageSetFromStock image icon IconSizeSmallToolbar)
                        )

updateProof' :: ProofFocus -> GState -> GState
updateProof' (p,path) gst = case (gProof gst,gExpr gst) of
                              (Just gpr,Just gexpr) -> upd gpr gexpr
                              (_,_) -> gst
    where upd gpr gexpr = gst { gProof = Just gpr { proof = (p,path)
                                                  }
                              , gExpr = Just $ gexpr { fExpr = fromJust $ getEnd p }
                              }
              where pr = proof gpr
                    e = fExpr gexpr

updateProof :: ProofFocus -> IState ()
updateProof = update . updateProof'

-- | Valida la prueba y actualiza el campo "validProof" del ProofState
updateValidProof :: IState ()
updateValidProof = getValidProof >>= \vp -> update (updateValidProof' vp)
    where updateValidProof' :: PM Proof -> GState -> GState
          updateValidProof' vp gst = case gProof gst of
                                       Just gpr -> gst { gProof = Just $ updPrf gpr }
                                       Nothing -> gst
          updPrf gpr = gpr { validProof = validateProof (toProof $ proof gpr) }

updateProofWidget pfw = update (\gst -> case gProof gst of
                                             Nothing -> gst
                                             Just gpr -> gst {gProof = Just gpr {
                                                     proofWidget = pfw}
                                             })


showProof :: IState ()
showProof = withRefValue $ uncurry putMsg . (status &&& show . proof . fromJust . gProof )


showProof' = getProof >>= io . debug . show


updateRelation :: Relation -> IState ()
updateRelation r = getProof >>= \(p,path) ->
                   updateProof (updateRel p r,path)
                   
updateAxiomBox :: HBox -> IState ()
updateAxiomBox b = update $ \gst -> gst {gProof = Just $ ((fromJust . gProof) gst) {axiomBox = b}}

addTheorem :: Theorem -> IState Theorem
addTheorem th = (update $ \gst -> gst { theorems = (th:theorems gst) }) >>
                return th

getTheorems :: IState [Theorem]
getTheorems = getStatePart theorems


getRelPF :: IState Relation
getRelPF = getProofState >>= \ps ->
            case ps of
                 Nothing -> return relEq
                 Just ps' -> 
                    getStatePart $ fromJust . getRel . fst . proof . fromJust . gProof
