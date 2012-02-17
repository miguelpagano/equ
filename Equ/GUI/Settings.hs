-- | Definición de elementos configurables. 
module Equ.GUI.Settings where

import Equ.GUI.Types (ExprStatus(..))


import Graphics.UI.Gtk
import Graphics.Rendering.Pango.Font

-- | Color del resaltado para mouse-over.
hoverBg :: Color
hoverBg = Color 0 32000 65000

-- | Color del resaltado para focused.
focusBg :: Color
focusBg =  Color 20000 60000 45000

whiteBg :: Color
whiteBg = Color 65000 65000 65000

grayBg :: Color
grayBg = Color 62000 61430 61180

axiomBg :: Color
axiomBg = Color 60000 58000 59000

errBg :: Color
errBg = Color 58000 18000 20000

successfulBg :: Color
successfulBg = Color 0 65000 2000

genericBg :: Color
genericBg = Color 61500 61500 61500

-- | Tamaño de entry-var para variables.
entryVarLength :: Int
entryVarLength = 10

-- | Ancho para la lista de símbolos.
paneSymbolWidth :: Int
paneSymbolWidth = 100

-- | Alto del sector para la construcción de fórmulas.
paneFormHeight :: Int
paneFormHeight = 30

-- | Alto del sector que informa sobre errores.
paneErrPaneHeight :: Int
paneErrPaneHeight = 100

-- | Símbolo para label donde todavía no hay nada ingresado.
emptyLabel :: String
emptyLabel = "..."

scrollInc :: Double
scrollInc = 10.0

scrollDec :: Double
scrollDec = - scrollInc


-- | Iconos para botones
typeTreeIcon = stockProperties
annotIcon = stockEdit
choicesIcon = stockIndex
addStepIcon = stockGoDown

-- | Iconos para estado de expresiones
imgState :: ExprStatus -> StockId
imgState Unknown = stockDialogQuestion
imgState Parsed =  stockDialogWarning
imgState NotParsed = stockDialogError
imgState TypeChecked = stockOk


-- | Estilo para nombre de axiomas o teoremas.
styleStepEvidence :: IO FontDescription
styleStepEvidence = fontItalic

-- | Estilo para títulos en info-boxes
styleInfoTitle ::  IO FontDescription
styleInfoTitle = fontBold

fontItalic :: IO FontDescription
fontItalic = fontDescriptionNew >>= \fd ->
             fontDescriptionSetStyle fd StyleItalic >>
             return fd


fontBold :: IO FontDescription
fontBold = fontDescriptionNew >>= \fd ->
           fontDescriptionSetWeight fd WeightBold >>
           return fd


