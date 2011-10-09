-- | Definición de elementos configurables. 
module Equ.GUI.Settings where

import Graphics.UI.Gtk

-- | Color del resaltado para mouse-over.
hoverBg :: Color
hoverBg = Color 0 32000 65000

-- | Color del resaltado para focused.
focusBg :: Color
focusBg = Color 0 65000 32000


-- | Tamaño de entry-var para variables.
entryVarLength :: Int
entryVarLength = 5

-- | Ancho para la lista de símbolos.
paneSymbolWidth :: Int
paneSymbolWidth = 100

-- | Alto del sector para la construcción de fórmulas.
paneFormHeight :: Int
paneFormHeight = 30