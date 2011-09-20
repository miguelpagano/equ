{-# Language GADTs #-}

{-| Este m&#243;dulo define la noci&#243;n de una prueba. -}
module Equ.Proof.Proof (
                  -- * Axiomas y teoremas
                   Basic(..)
                 , Axiom(..)
                 , Theorem(..)
                 , Truth(..)
                 -- * Pruebas
                 -- $proofs
                 , Proof(..)
                 , Ctx 
                 -- * Ejemplos
                 -- $samples
                 , getCtx
                 , getStart
                 , getEnd
                 , isHole
                 ) where


import Equ.Expr
import Equ.PreExpr
import Equ.Rule
import Equ.Theories.FOL(neuterEquiv_Rule1,equiv,true)

import Data.Text (Text,pack)
import Data.Map (Map,empty)
import Data.Monoid
import Data.Maybe

-- | Las hip&#243;tesis son nombradas por n&#250;meros.
data Name = Index Int
    deriving (Show,Ord,Eq)

-- | La clase Truth representa una verdad en una teoría. En principio
-- pensamos en Axiomas y Teoremas.
class Truth t where
    truthName  :: t -> Text
    truthExpr  :: t -> Expr
    truthRel   :: t -> Relation
    truthRules :: t -> [Rule]    
    truthBasic :: t -> Basic

-- | Un axioma es una expresi&#243;n que puede ser interpretada como varias
-- reglas de re-escritura.
data Axiom = Axiom {
      axName  :: Text 
    , axExpr  :: Expr
    , axRel   :: Relation
    , axRules :: [Rule] 
    }
    deriving (Eq,Show)

-- | Instancia de Truth para el tipo Axiom.
instance Truth Axiom where
    truthName  = axName
    truthExpr  = axExpr
    truthRel   = axRel
    truthRules = axRules
    truthBasic = Ax

-- |  Un   teorema  tambi&#233;n  permite,  como   un  axioma,  re-escribir
-- expresiones; a  diferencia de un  axioma debe tener una  prueba que
-- demuestre su validez.
data Theorem = Theorem {
      thName  :: Text
    , thExpr  :: Expr
    , thRel   :: Relation
    , thProof :: Proof
    , thRules :: [Rule]
    }
    deriving (Eq,Show)

-- | Instancia de Truth para el tipo theorem.
instance Truth Theorem where
    truthName  = thName
    truthExpr  = thExpr
    truthRel   = thRel
    truthRules = thRules
    truthBasic = Theo

-- | El contexto lleva las hip&#243;tesis actuales; en nuestro caso hay
-- tres formas de agregar hip&#243;tesis al contexto: en una prueba por
-- casos hay nuevas igualdades; en una prueba por inducci&#243;n hay
-- hip&#243;tesis inductivas y en una prueba que usa el metateorema de la
-- deducci&#243;n asumimos el antecedente de una implicaci&#243;n.
type Ctx = Map Name Expr

-- | Las pruebas elementales son aplicar un axioma (en un foco), 
-- usar un teorema ya probado, o usar una hip&#243;tesis.
data Basic where
    Ax  :: Axiom -> Basic    -- Un axioma de cierta teor&#237;a.
    Theo :: Theorem -> Basic  -- Un teorema ya probado.
    Hyp :: Name -> Basic   --  Una hip&#243;tesis que aparece en el contexto.               
    deriving (Eq,Show)

{- $proofs

[@Simple@] 
  La propiedad importante es que en los pasos simples
  tenemos alguna regla asociada al axioma o al teorema usado que hace
  coincidir (salvo variables ligadas?) a la primera con la segunda
  expresi&#243;n:

Si 

@
proofAx :: Proof
proofAx = Simple ctx foc foc' $ Ax ax

proofThm :: Proof
proofThm = Simple ctx foc foc' $ Theo thm
@

entonces @ rewriteInFocus foc ax == foc' @ y @ rewriteInFocus foc thm == foc' @.

Si la prueba es simple y fue usando una hip&#243;tesis, digamos

@
proofHyp :: Proof
proofHyp = Simple ctx foc foc' $ Hyp n
@ 

entonces @length ctx > n@ y @rewriteInFocus foc (ctx!n) == foc'@.

[@Transitividad@] 

Una prueba por transitividad 

@
theoTrans :: Proof
theoTrans = Trans ctx rel fe fe1 fe2 prf prf' 
@

es una prueba de @fe rel fe2@ usando pruebas intermedias @prf@ de @fe
rel fe1@ y @prf'@ de @fe1 rel fe2@. 

[Casos]

En una prueba por casos

@
theoCases :: Proof
theoCases = Cases ctx rel fe1 fe2 c [(f1,p1),..,(fn,pn)]
@

hacemos an&#225;lisis por casos en @c@, esto es posible dependiendo
del tipo de @c@; por ejemplo si @type c == TyConst ATyNat@, entonces
podemos introducir los casos @c == 0@, @c==1@, @c > 1@. La lista de
focos y pruebas consiste en tantas pruebas como casos se hayan
considerando; cada par @(fi,pi)@ representa una prueba de @fe1 rel
fe2@ a&#241;adiendo la hip&#243;tesis extra @fi@ en @ctx@.

[Inducci&#243;n]

La prueba por inducci&#243;n es similar a la prueba por casos, excepto
que en los casos inductivos podemos usar la hip&#243;tesis
inductiva. Para entender este tipo de pruebas utilicemos el siguiente
ejemplo de inducci&#243;n en los naturales:

@&#9001; &#8704; n : : &#9001; &#8721; i : 0 &#8804; i &#8804; n : i &#9002; = n * (n + 1) / 2 &#9002;@

para probarlo utilizamos inducci&#243;n en @n@ (notemos que impl&#237;citamente
estamos utilizando el meta-teorema que dice que para probar una
cuantificaci&#243;n universal podemos elegir un elemento arbitrario del
dominio cuantificado y probar la matriz de la f&#243;rmula); ahora queremos
probar 

@&#9001; &#8721; i : 0 &#8804; i &#8804; n : i &#9002; = n * (n + 1) / 2@ 

donde @n@ es ahora una variable libre. Usar inducci&#243;n en @n@ entonces implica
construir una prueba de 

@&#9001; &#8721; i : 0 &#8804; i &#8804; 0 : i &#9002; = 0 * (0 + 1) / 2@

y otra prueba de 

@&#9001; &#8721; i : 0 &#8804; i &#8804; (k+1) : i &#9002; = (k+1) * ((k+1) + 1) / 2@

con la hip&#243;tesis inductiva como una hip&#243;tesis adicional en el contexto:

@
&#9001; &#8721; i : 0 &#8804; i &#8804; k : i &#9002; = k * (k+1) / 2 .
@

El constructor @Ind@ permite pruebas por inducci&#243;n en varias
sub-expresiones @e1,...,en@; la segunda lista es la lista de pruebas
correspondiente a todos los casos de acuerdo a los tipos de las
expresiones sobre las que hacemos inducci&#243;n. Inicialmente podemos
pensar que s&#243;lo haremos inducci&#243;n en los naturales y que @[e1,...,en]@
tiene un s&#243;lo elemento: la variable sobre la que hacemos inducci&#243;n;
por lo tanto @[(fs1,p1),...,(fsm,pm)]@ ser&#237;a una lista con dos elementos
@[(n=0,proofBaseCase),(n=k+1,proofInd)]@.

@
theoInd :: Proof
theoInd = Ind ctx rel fe1 fe2 [e1,...,en] [(fs1,p1),...,(fsm,pm)]
@

[Meta-teorema de la deducci&#243;n]

El meta-teorema de la deducci&#243;n est&#225; representado por el constructor
@Deduc@ y permite construir una prueba de @p &#8658; q@ a partir de una
prueba de @q@ agregando @p@ a las hip&#243;tesis; por ejemplo, si
@proofQ :: Proof@ con @lhs proofQ == q@, @rhs proofQ == True@,
@p `in` ctx proofQ@ entonces el siguiente t&#233;rmino es una prueba
de @p &#8658; q@:

@
theoDeduc :: Proof
theoDeduc = Deduc ctx relImpl p q prf
@

[Sub-pruebas in-situ]

En general las pruebas (sean estos pasos elementales o m&#225;s
complicados) implican la prueba de una relaci&#243;n entre dos expresiones
pero donde se reescribe una sub-expresi&#243;n; esa reescritura es una
prueba sencilla necesariamente. @Focus@ permite que reescribamos una
sub-expresi&#243;n sin usar un teorema previamente demostrado sino con una
prueba in-situ. Por ejemplo, en la siguiente expresi&#243;n, @prf@ es una
prueba de @e == e'@.

@
theoFocus :: Proof
theoFocus = Focus ctx rel (e,p) (e',p') prf 
@

-}

data Proof where
    Reflex :: Proof
    Hole   :: Ctx -> Relation -> Focus -> Focus -> Proof 
    Simple :: Ctx -> Relation -> Focus -> Focus -> Basic -> Proof
    Trans  :: Ctx -> Relation -> Focus -> Focus -> Focus -> Proof -> Proof -> Proof
    Cases  :: Ctx -> Relation -> Focus -> Focus -> Focus -> [(Focus,Proof)] -> Proof
    Ind    :: Ctx -> Relation -> Focus -> Focus -> [Focus] -> [([Focus],Proof)] -> Proof
    Deduc  :: Ctx -> Focus -> Focus -> Proof -> Proof
    Focus  :: Ctx -> Relation -> Focus -> Focus -> Proof -> Proof
    deriving (Eq,Show)

instance Monoid Proof where
    mempty = Reflex
    mappend Reflex p = p
    mappend p Reflex = p
    mappend p1 p2 = Trans (fromJust $ getCtx p1) (fromJust $ getRel p1) (fromJust $ getStart p1) 
                          (fromJust $ getStart p2) (fromJust $ getEnd p2) p1 p2
    


isHole :: Proof -> Bool
isHole (Hole c _ _ _) = True
isHole _ = False

getCtx :: Proof -> Maybe Ctx
getCtx Reflex = Nothing
getCtx (Hole c _ _ _) = Just c
getCtx (Simple c _ _ _ _) = Just c
getCtx (Trans c _ _ _ _ _ _) = Just c
getCtx (Cases c _ _ _ _ _) = Just c
getCtx (Ind c _ _ _ _ _) = Just c
getCtx (Deduc c _ _ _) = Just c
getCtx (Focus c _ _ _ _) = Just c


-- DUDA: Que hacemos con Reflex aca??
getStart :: Proof -> Maybe Focus
getStart Reflex = Nothing
getStart (Hole _ _ f _) = Just f
getStart (Simple _ _ f _ _) = Just f
getStart (Trans _ _ f _ _ _ _) = Just f
getStart (Cases _ _ f _ _ _) = Just f
getStart (Ind _ _ f _ _ _) = Just f
getStart (Deduc _ f _ _) = Just f
getStart (Focus _ _ f _ _) = Just f

getEnd :: Proof -> Maybe Focus
getEnd Reflex = Nothing
getEnd (Hole _ _ _ f) = Just f
getEnd (Simple _ _ _ f _) = Just f
getEnd (Trans _ _ _ f _ _ _) = Just f
getEnd (Cases _ _ _ f _ _) = Just f
getEnd (Ind _ _ _ f _ _) = Just f
getEnd (Deduc _ _ f _) = Just f
getEnd (Focus _ _ _ f _) = Just f

-- | Devuelve la relación para la cual es una prueba.
getRel :: Proof -> Maybe Relation
getRel Reflex = Nothing
getRel (Hole _ r _ _) = Just r
getRel (Simple _ r _ _ _) = Just r
getRel (Trans _ r _ _ _ _ _) = Just r
getRel (Cases _ r _ _ _ _) = Just r
getRel (Ind _ r _ _ _ _) = Just r
getRel (Deduc _ _ _ _) = Just relImpl
getRel (Focus _ r _ _ _) = Just r

{- $samples

[Axiomas]

-}
-- neutralEquiv :: Axiom
-- neutralEquiv = Axiom { axName = pack "Neutro de la equivalencia"
--                      , axExpr = Expr $ parser "(p ≡ True) ≡ p"
--                      , axRel = relEquiv
--                      , axRules = [neuterEquiv_Rule1]
--                      }
-- {-
-- 
-- [Pruebas]
-- 
-- @
-- incomplete :: Proof
-- incomplete = Hole M.empty Equivalence (Top,equiv True True) (Top,True)
-- @
-- 
-- -}
-- 
-- trivial :: Proof
-- trivial = Simple empty relEquiv (toFocus reflTrue) (toFocus true') $
--           Ax neutralEquiv
--     where (Expr true') = true
--           (Expr reflTrue) = true `equiv` true
-- 
-- trivialBack :: Proof
-- trivialBack = Simple empty relEquiv (toFocus true') (toFocus reflTrue) $
--               Ax neutralEquiv
--     where (Expr true') = true
--           (Expr reflTrue) = true `equiv` true
-- 
-- trivial' :: Proof
-- trivial' = Simple empty relEquiv foc foc $ Ax neutralEquiv
--     where (Expr true') = true
--           foc = toFocus true'
-- 
-- 
-- -- | Ejemplo, muy pavo, de prueba usando transitividad.
-- transEx :: Proof
-- transEx = Trans empty relEquiv foc (toFocus true') foc trivial trivialBack
--     where (Expr reflTrue) = true `equiv` true
--           (Expr true') = true
--           foc = toFocus reflTrue
-- 
-- 
-- -- | Ejemplo, muy pavo, de prueba usando transitividad con un hueco.
-- transExHole :: Proof
-- transExHole = Trans empty relEquiv foc foc' foc trivial step
--     where (Expr reflTrue) = true `equiv` true
--           (Expr true') = true
--           foc = toFocus reflTrue
--           foc' = toFocus true'
--           hole = Hole empty relEquiv foc' foc'
--           step = Trans empty relEquiv foc' foc' foc hole trivialBack
