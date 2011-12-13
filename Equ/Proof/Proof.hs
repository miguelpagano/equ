{-# Language GADTs, TypeSynonymInstances #-}

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
                 , isHole
                 -- Proyecciones
                 , getCtx, getStart, getEnd, getRel
                 , updateStart, updateEnd, updateRel, updateMiddle
                 ) where

import Equ.Expr
import Equ.PreExpr
import Equ.Rule

import Data.Text (Text, unpack)
import Data.Map (Map, fromList)
import Data.Monoid
import Data.Maybe
import Data.Serialize(Serialize, get, getWord8, put, putWord8)

import Control.Applicative ((<$>), (<*>))
import Test.QuickCheck


-- | Las hip&#243;tesis son nombradas por n&#250;meros.
data Name = Index Int
    deriving (Show,Ord,Eq)

instance Arbitrary Name where
    arbitrary = Index <$> arbitrary

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
    deriving Eq

instance Show Axiom where
    --show ax = (show . unpack . axName) ax ++ ": " ++ (show . axExpr) ax
    show ax = (show . unpack . axName) ax
    
instance Arbitrary Axiom where
    arbitrary = Axiom <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary

instance Serialize Axiom where
    put (Axiom n e r lru) = put n >> put e >> put r >> put lru
    get = Axiom <$> get <*> get <*> get <*> get

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
    deriving Eq
    

instance Show Theorem where
    show th = (show . unpack . thName) th ++ ": " ++ (show . thExpr) th
            

instance Arbitrary Theorem where
    arbitrary = Theorem <$> arbitrary <*> arbitrary <*> 
                            arbitrary <*> arbitrary <*> arbitrary

instance Serialize Theorem where
    put (Theorem n e r p lru) = put n >> put e >> put r >> put p >> put lru
    get = Theorem <$> get <*> get <*> get <*> get <*> get

-- | Instancia de Truth para el tipo theorem.
instance Truth Theorem where
    truthName  = thName
    truthExpr  = thExpr
    truthRel   = thRel
    truthRules = thRules
    truthBasic = Theo

data Hypothesis = Hypothesis {
     hypName :: Text
   , hypExpr :: Expr
   , hypRel  :: Relation
   , hypRule :: Rule
}
    deriving (Eq,Show)

instance Truth Hypothesis where
    truthName = hypName
    truthExpr = hypExpr
    truthRel  = hypRel
    truthRules = (\r -> r:[]) . hypRule
    truthBasic = Hyp

instance Arbitrary Hypothesis where
    arbitrary = Hypothesis <$> arbitrary <*> arbitrary <*> 
                            arbitrary <*> arbitrary
                            
instance Serialize Hypothesis where
    put _ = undefined
    get = undefined
    
-- | El contexto lleva las hip&#243;tesis actuales; en nuestro caso hay
-- tres formas de agregar hip&#243;tesis al contexto: en una prueba por
-- casos hay nuevas igualdades; en una prueba por inducci&#243;n hay
-- hip&#243;tesis inductivas y en una prueba que usa el metateorema de la
-- deducci&#243;n asumimos el antecedente de una implicaci&#243;n.
type Ctx = Map Name Hypothesis

instance Arbitrary Ctx where
    arbitrary = fromList <$> arbitrary

-- | Las pruebas elementales son aplicar un axioma (en un foco), 
-- usar un teorema ya probado, o usar una hip&#243;tesis.
data Basic where
    Ax  :: Axiom -> Basic    -- Un axioma de cierta teor&#237;a.
    Theo :: Theorem -> Basic  -- Un teorema ya probado.
    Hyp :: Hypothesis -> Basic   --  Una hip&#243;tesis que aparece en el contexto.               
    deriving (Show, Eq)
    
instance Truth Basic where
    truthName (Ax a) = axName a
    truthName (Theo t) = thName t
    truthName (Hyp h) = hypName h
    truthExpr (Ax a) = axExpr a
    truthExpr (Theo t) = thExpr t
    truthExpr (Hyp h) = hypExpr h
    truthRel (Ax a) = axRel a
    truthRel (Theo t) = thRel t
    truthRel (Hyp h) = hypRel h
    truthRules (Ax a) = axRules a
    truthRules (Theo t) = thRules t
    truthRules (Hyp h) = [hypRule h]
    truthBasic b = b
    
-- 
instance Arbitrary Basic where
    arbitrary = 
        oneof [ Ax <$> arbitrary
              , Theo <$> arbitrary
              , Hyp <$> arbitrary
              ]
-- 
instance Serialize Basic where
    put (Ax a) = putWord8 0 >> put a
    put (Theo t) = putWord8 1 >> put t
    put (Hyp h) = putWord8 2 >> put h
    
    get = getWord8 >>= \tag_ ->
          case tag_ of
            0 -> Ax <$> get
            1 -> Theo <$> get
            2 -> Hyp <$> get
            _ -> fail $ "SerializeErr Basic " ++ show tag_

--             
--             
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

    deriving Eq
{-    
instance Eq Proof where
    Reflex == Reflex = True
    Reflex == _ = False
    _ == Reflex = False
    p1 == p2 = (fromJust $ getStart p1) == (fromJust $ getStart p2) &&
               (fromJust $ getEnd p1) == (fromJust $ getEnd p2)-}
    

instance Show Proof where
    show Reflex = ""
    show (Hole _ r f f') = "Hole " ++ show r ++ " " ++ show (fst f) ++ " " ++ show (fst f')
    show (Simple _ r f f' b) = "Simple " ++ show r ++ " " ++ show (fst f) ++ " " ++ show (fst f') ++ " { " ++ show b ++" } "
    show (Trans _ r f f' f'' p p') = "Trans " ++ show r ++ " " ++ show (fst f) ++ " " ++ 
                                                 show (fst f') ++ " " ++ show (fst f'') ++ " { " ++ show p ++ " } " ++
                                                 " { " ++ show p' ++ " } "
    show _ = "prueba no implementada"

-- Hace falta mejorar esta instancia.
-- instance Show Proof where
--     show Reflex = ""
--     show (Hole _ r f f') = "\t" ++ show (fst f) ++ "\n" ++ show r ++ "{ ? }" ++  "\n\t" ++ show (fst f')
--     show (Simple _ r f f' b) = "\t" ++ show (fst f) ++ 
--                                  "\n" ++ show r ++ "{" ++ show b ++ "}" ++ 
--                                  "\n\t" ++ show (fst f')
--     show (Trans _ r f f' f'' p p') =  "\t" ++ show (fst f) ++ 
--                                         "\n" ++ show r ++ "\n{" ++ show p ++
--                                         "\n\t\n}\n\t" ++ show (fst f'') ++ 
--                                         "\n" ++ show r ++ "\n{" ++ show p' ++ 
--                                         "\n\t\n}\n\t" ++ show (fst f')
--     show (Cases _ r f f' f'' lfp) = show r ++ show f ++ show f' ++ 
--                                       show f'' ++ show lfp
--     show (Ind _ r f f' lf lfp) = show r ++ show f ++ show f' ++ 
--                                       show lf ++ show lfp
--     show (Deduc _ f f' p) = show f ++ show f' ++ show p
--     show (Focus _ r f f' p) = show r ++ show f ++ show f' ++ show p

{- Instancia Arbitrary para Proof, la definición de arbitrary la realizamos
    con sized ya que si no las pruebas crecen descontroladamente y como
    consecuencia al correr los test se produce un colapso de memoria.
    
    Para solucionar este problema encontré dos opciones rápidas usando 
    herramientas que nos provee quickcheck. Una es usar la función sized
    y la otra alternativa es usar frequency. Esta ultima fue la primera opción
    que use pero despues estudiando un poco mas parece que siempre que queremos
    generar estructuras recursivas lo ideal es usar sized para asegurar la
    finalizacion y ademas prevenir resultados demasiado grandes.
    
    Algo importante a comentar sobre la función sized, es que utiliza un size
    implícito en quickcheck, el cual no tiene una utilización fija, tan así 
    que a veces ni siquiera es usado.
    
    Dejo la instancia primera que había hecho por si hay algo que discutir.
    arbitrary nos queda definido, gracias a frequency, de la siguiente manera;
    de cada 100 pruebas generadas, 50 son Simples, 45 son Hole, 1 Trans, 
    1 Cases, 1 Ind, 1 Deduc, 1 Focus.
    Nota: La desición acerca de esta frecuentcia la tome basándome en algunos
        test que hice, así como esta nos podemos asegurar que la corrida de 
        testeo termina.
        
    arbitrary =
        frequency [ (45, Hole <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary)
                  , (50, Simple <$> arbitrary <*> arbitrary <*> 
                               arbitrary <*> arbitrary <*> arbitrary)
                  , (1, Trans <$> arbitrary <*> arbitrary <*> arbitrary <*> 
                              arbitrary <*> arbitrary <*> arbitrary <*> arbitrary)
                  , (1, Cases <$> arbitrary <*> arbitrary <*> arbitrary <*> 
                              arbitrary <*> arbitrary <*> arbitrary)
                  , (1, Ind <$> arbitrary <*> arbitrary <*> arbitrary <*> 
                              arbitrary <*> arbitrary <*> arbitrary)
                  , (1, Deduc <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary)
                  , (1, Focus <$> arbitrary <*> arbitrary <*> 
                              arbitrary <*> arbitrary <*> arbitrary)
                  ]

-}

instance Arbitrary Proof where
    arbitrary = sized proof
        where
            proof :: Int -> Gen Proof
            proof 0 = 
                oneof [ return Reflex
                      , Hole <$> arbitrary <*> arbitrary <*> 
                                 arbitrary <*> arbitrary
                      , Simple <$> arbitrary <*> arbitrary <*> 
                                   arbitrary <*> arbitrary <*> arbitrary
                      ]
            proof n | n > 0 = 
                oneof [ return Reflex
                      , Hole <$> arbitrary <*> arbitrary <*> 
                                 arbitrary <*> arbitrary
                      , Simple <$> arbitrary <*> arbitrary <*> 
                                   arbitrary <*> arbitrary <*> arbitrary
                      , Trans <$> arbitrary <*> arbitrary <*> arbitrary <*> 
                                  arbitrary <*> arbitrary <*> 
                                  subProof <*> subProof
                      , Cases <$> arbitrary <*> arbitrary <*> arbitrary <*> 
                                  arbitrary <*> arbitrary <*> listPairFocusProof
                      , Ind <$> arbitrary <*> arbitrary <*> arbitrary <*> 
                                arbitrary <*> arbitrary <*> 
                                listPPFocusProof
                      , Deduc <$> arbitrary <*> arbitrary <*> 
                                  arbitrary <*> subProof
                      , Focus <$> arbitrary <*> arbitrary <*> 
                                  arbitrary <*> arbitrary <*> subProof
                    ]
                where   
                    -- Disminuimos el largo (visto como un arbol) de la prueba.
                    subProof :: Gen Proof
                    subProof = proof (n `div` 10)
                    pairFocusProof :: Gen (Focus, Proof)
                    pairFocusProof = (,) <$> arbitrary <*> subProof
                    listPairFocusProof :: Gen [(Focus, Proof)]
                    listPairFocusProof = vectorOf 2 pairFocusProof
                    pPFocusProof :: Gen ([Focus], Proof)                    
                    pPFocusProof = (,) <$> arbitrary <*> subProof
                    listPPFocusProof :: Gen [([Focus], Proof)]
                    listPPFocusProof = vectorOf 2 pPFocusProof

instance Serialize Proof where
    put Reflex = putWord8 0
    put (Hole ctx r f f') = putWord8 1 >> put ctx >> put r >>  put f >> put f'
    put (Simple ctx r f f' b) = 
        putWord8 2 >> put ctx >> put r >> put f >> put f' >> put b
    put (Trans ctx r f f' f'' p p') = 
        putWord8 3 >> put ctx >> put r >> put f >> put f' >> put f'' >>
                      put p >> put p'
    put (Cases ctx r f f' f'' lfp) = 
        putWord8 4 >> put ctx >> put r >> put f >> put f' >> put f'' >> put lfp
    put (Ind ctx r f f' lf llfp) = 
        putWord8 5 >> put ctx >> put r >> put f >> put f' >> put lf >> put llfp
    put (Deduc ctx f f' p) = putWord8 6 >> put ctx >> put f >> put f' >> put p
    put (Focus ctx r f f' p) = 
        putWord8 7 >> put ctx >> put r >> put f >> put f' >> put p
    
    get = getWord8 >>= \tag_ ->
          case tag_ of
            0 -> return Reflex 
            1 -> Hole <$> get <*> get <*> get <*> get
            2 -> Simple <$> get <*> get <*> get <*> get <*> get
            3 -> Trans <$> get <*> get <*> get <*> get <*> get <*> get <*> get
            4 -> Cases <$> get <*> get <*> get <*> get <*> get <*> get
            5 -> Ind <$> get <*> get <*> get <*> get <*> get <*> get
            6 -> Deduc <$> get <*> get <*> get <*> get
            7 -> Focus <$> get <*> get <*> get <*> get <*> get
            _ -> fail $ "SerializeErr Proof " ++ show tag_

instance Serialize Name where
    put (Index i) = putWord8 0 >> put i

    get = getWord8 >>= \tag_ -> 
          case tag_ of
            0 -> Index <$> get
            _ -> fail $ "SerializeErr Name " ++ show tag_

instance Monoid Proof where
    mempty = Reflex
    mappend Reflex p = p
    mappend p Reflex = p
    mappend p1 p2 = Trans (fromJust $ getCtx p1) (fromJust $ getRel p1) 
                          (fromJust $ getStart p1) (fromJust $ getEnd p2) 
                          (fromJust $ getStart p2) p1 p2

isHole :: Proof -> Bool
isHole (Hole _ _ _ _) = True
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


updateStart :: Proof -> Focus -> Proof
updateStart Reflex _ = Reflex
updateStart (Hole c r _ f2) f = Hole c r f f2
updateStart (Simple c r _ f2 b) f = Simple c r f f2 b
updateStart (Trans c r _ f2 fm p p') f = Trans c r f fm f2 (updateStart p f) p'
updateStart (Cases c r _ f2 fc list) f = Cases c r f f2 fc list
updateStart (Ind c r _ f2 l1 l2) f = Ind c r f f2 l1 l2
updateStart (Deduc c _ f2 p) f = Deduc c f f2 p
updateStart (Focus c r _ f2 p) f = Focus c r f f2 p

updateEnd :: Proof -> Focus -> Proof
updateEnd Reflex f = Reflex
updateEnd (Hole c r f1 _) f = Hole c r f1 f
updateEnd (Simple c r f1 _ b) f = Simple c r f1 f b
updateEnd (Trans c r f1 _ fm p p') f = Trans c r f1 f fm p (updateEnd p' f)
updateEnd (Cases c r f1 _ fc list) f = Cases c r f1 f fc list
updateEnd (Ind c r f1 _ l1 l2) f = Ind c r f1 f l1 l2
updateEnd (Deduc c f1 _ p) f = Deduc c f1 f p
updateEnd (Focus c r f1 _ p) f = Focus c r f1 f p

updateMiddle :: Proof -> Focus -> Proof
updateMiddle (Trans c r f1 f2 _ p p') f = Trans c r f1 f2 f (updateEnd p f) (updateStart p' f)
updateMiddle _ f = undefined

updateRel :: Proof -> Relation -> Proof
updateRel Reflex r = Reflex
updateRel (Hole c _ f1 f2) r = Hole c r f1 f2
updateRel (Simple c _ f1 f2 b) r = Simple c r f1 f2 b
updateRel (Trans c _ f1 f2 fm p p') r = Trans c r f1 f2 fm p p'
updateRel (Cases c _ f1 f2 fc list) r = Cases c r f1 f2 fc list
updateRel (Ind c _ f1 f2 l1 l2) r = Ind c r f1 f2 l1 l2
updateRel (Deduc c f1 f2 p) r = Deduc c f1 f2 p
updateRel (Focus c _ f1 f2 p) r = Focus c r f1 f2 p


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
