module Equ.GUI.Proof.RelationList where

import Equ.GUI.Types hiding (GState)
import Equ.GUI.Utils

import Equ.Rule
import Equ.Theories

import Graphics.UI.Gtk hiding (eventButton, eventSent,get)
import Graphics.UI.Gtk.Gdk.EventM

import Data.Maybe(fromJust)
import Data.Text(unpack)
import Data.List(elemIndex)


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

defaultRelation :: Relation
defaultRelation = head $ relationList