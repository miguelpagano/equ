{-# Language GADTs #-}

{-| Este m&#243;dulo define la noci&#243;n de una prueba. -}
module Equ.Proof (
                  -- * Axiomas y teoremas
                   Axiom
                 , Theorem
                 -- * Pruebas
                 -- $proofs
                 , Proof
                 -- * Ejemplos
                 -- $samples
                 ) where


import Equ.Expr
import Equ.PreExpr
import Equ.Theories
import Equ.Rule
import Equ.Rewrite
import Equ.Theories.FOL

import Equ.Parser

import qualified Data.Text as T
import qualified Data.Map as M
import Control.Monad


-- | Las hip&#243;tesis son nombradas por n&#250;meros.
data Name = Index Int
    deriving (Show,Ord,Eq)

-- | La clase Truth representa una verdad en una teoría. En principio
-- pensamos en Axiomas y Teoremas.
class Truth t where
    truthName  :: t -> T.Text
    truthExpr  :: t -> Expr
    truthRel   :: t -> Relation
    truthRules :: t -> [Rule]

-- | Un axioma es una expresi&#243;n que puede ser interpretada como varias
-- reglas de re-escritura.
data Axiom = Axiom {
      axName  :: T.Text 
    , axExpr  :: Expr
    , axRel   :: Relation
    , axRules :: [Rule] 
    }
    deriving Show

-- | Instancia de Truth para el tipo Axiom.
instance Truth Axiom where
    truthName  = axName
    truthExpr  = axExpr
    truthRel   = axRel
    truthRules = axRules
    
-- |  Un   teorema  tambi&#233;n  permite,  como   un  axioma,  re-escribir
-- expresiones; a  diferencia de un  axioma debe tener una  prueba que
-- demuestre su validez.
data Theorem = Theorem {
      thName  :: T.Text
    , thExpr  :: Expr
    , thRel   :: Relation
    , thProof :: Proof
    , thRules :: [Rule]
    }
    deriving Show

-- | Instancia de Truth para el tipo theorem.
instance Truth Theorem where
    truthName  = thName
    truthExpr  = thExpr
    truthRel   = thRel
    truthRules = thRules

-- | El contexto lleva las hip&#243;tesis actuales; en nuestro caso hay
-- tres formas de agregar hip&#243;tesis al contexto: en una prueba por
-- casos hay nuevas igualdades; en una prueba por inducci&#243;n hay
-- hip&#243;tesis inductivas y en una prueba que usa el metateorema de la
-- deducci&#243;n asumimos el antecedente de una implicaci&#243;n.
type Ctx = M.Map Name Expr

-- | Las pruebas elementales son aplicar un axioma (en un foco), 
-- usar un teorema ya probado, o usar una hip&#243;tesis.
data Basic where
    Ax  :: Axiom -> Basic    -- Un axioma de cierta teor&#237;a.
    Theo :: Theorem -> Basic  -- Un teorema ya probado.
    Hyp :: Name -> Basic   --  Una hip&#243;tesis que aparece en el contexto.               
    deriving Show

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
    Hole   :: Ctx -> Relation -> Focus -> Focus -> Proof 
    Simple :: Ctx -> Relation -> Focus -> Focus -> Basic -> Proof
    Trans  :: Ctx -> Relation -> Focus -> Focus -> Focus -> Proof -> Proof -> Proof
    Cases  :: Ctx -> Relation -> Focus -> Focus -> Focus -> [(Focus,Proof)] -> Proof
    Ind    :: Ctx -> Relation -> Focus -> Focus -> [Focus] -> [([Focus],Proof)] -> Proof
    Deduc  :: Ctx -> Focus -> Focus -> Proof -> Proof
    Focus  :: Ctx -> Relation -> Focus -> Focus -> Proof -> Proof
    deriving Show

getCtx :: Proof -> Ctx
getCtx (Hole c _ _ _) = c
getCtx (Simple c _ _ _ _) = c
getCtx (Trans c _ _ _ _ _ _) = c
getCtx (Cases c _ _ _ _ _) = c
getCtx (Ind c _ _ _ _ _) = c
getCtx (Deduc c _ _ _) = c
getCtx (Focus c _ _ _ _) = c


{- $samples

[Axiomas]

-}
neutralEquiv :: Axiom
neutralEquiv = Axiom { axName = T.pack "Neutro de la equivalencia"
                     , axExpr = Expr $ parser "(p ≡ True) ≡ p"
                     , axRel = relEquiv
                     , axRules = [neuterEquiv_Rule1]
                     }
{-

[Pruebas]

@
incomplete :: Proof
incomplete = Hole M.empty Equivalence (Top,equiv True True) (Top,True)
@

@
trivial :: Proof
trivial = Simple M.empty Equivalence (Top,equiv True True) (Top,True) $
          Ax neutralEquiv
@


-}

-- Faltaría definir un buen conjunto de errores para las pruebas.
data ProofError = Rewrite RewriteError 
                | BasicNotApplicable Basic
                | ProofError
    deriving Show

{- 
Funciones para construir y manipular pruebas.
Este kit de funciones debería proveer todas las herramientas
necesarias para desarrollar pruebas en equ 
-}

firstProof :: [Either ProofError Proof] -> Either ProofError Proof
firstProof = headWithDefault ProofError . filter predicate
    where
        headWithDefault :: ProofError -> [Either ProofError Proof] -> Either ProofError Proof
        headWithDefault def [] = Left def
        headWithDefault def l = head l
        predicate :: Either ProofError Proof -> Bool
        predicate (Left _) = False
        predicate (Right p) = True

-- Funcion para checkear igualdad, con la variante importante que en caso de
-- no cumplirse devolvemos un resultado por default.
checkEqWithDefault :: Eq a => d -> a -> a -> Either d Bool
checkEqWithDefault def a b | a /= b = Left def
                           | otherwise = Right True


{- 
Funciones para construir y manipular pruebas.
Este kit de funciones debería proveer todas las herramientas
necesarias para desarrollar pruebas en equ 
-}

proofFromRule :: Truth t => Focus -> Focus -> Relation -> t -> (t -> Basic) ->
                            Rule -> Either ProofError Proof
proofFromRule f1 f2 rel t basicCons r = 
    case (focusedRewrite f1 r) of
        Left er  ->  Left $ Rewrite er
        Right f ->  checkEqWithDefault (BasicNotApplicable (basicCons t))
                                        rel (truthRel t) >>
                    checkEqWithDefault (BasicNotApplicable (basicCons t))
                                        f f2 >>=
                    \_ -> Right $ Simple M.empty rel f1 f2 (basicCons t)


firstRight :: Either a b -> [Either a b] -> Either a b
firstRight (Left a) [] = Left a
firstRight (Left _) (e:es) = firstRight e es
firstRight (Right b) _ = Right b

-- | Dados dos focuses f1 y f2, una relacion rel y un axioma a, intenta crear una prueba
-- para f1 rel f2, utilizando el paso simple de aplicar el axioma a.
proofFromAxiom :: Focus -> Focus -> Relation -> Axiom -> Either ProofError Proof
proofFromAxiom f1 f2 rel a = firstRight (Left $ BasicNotApplicable $ Ax a) $ 
                           map (proofFromRule f1 f2 rel a Ax) (truthRules a) 

-- | Dados dos focuses f1 y f2, una relacion rel y un teorema t, intenta crear una prueba
-- para f1 rel f2, utilizando el paso simple de aplicar el teorema t.
proofFromTheorem :: Focus -> Focus -> Relation -> Theorem -> Either ProofError Proof
proofFromTheorem f1 f2 rel t = firstRight (Left $ BasicNotApplicable $ Theo t) $ 
                           map (proofFromRule f1 f2 rel t Theo) (truthRules t) 



{- 
Estrategia de prueba secuencial, agregando pasos transitivos.
Tenemos un tipo EstTrans, que lo utilizamos para llevar la estrategia.
Tenemos los invariantes de que hay un SOLO hueco. Y la prueba está terminada
cuando eliminamos ese hueco.
EstTrans f f1 fn g P01 Png representa una secuencia de pruebas, donde se quiere
demostrar f rel g. P01 es una prueba para f rel f1, Png es una prueba para fn rel g.
No tenemos prueba para f1 rel fn, por lo que ahí está el hueco.
Si queremos agregar un paso a la prueba, podemos hacerlo de dos formas, desde "arriba"
o desde "abajo". 
Un paso desde "abajo" será agregar proveer un nuevo foco f2, y una prueba para f1 rel f2 = P12
El resultante será:
EstTrans f f2 fn g P02 Png, donde P02 = Trans f f1 f2 P01 P12, y entre f2 y fn tenemos un hueco.
Un paso desde "arriba" será similar, solo que agregamos un nuevo foco fn-1, y una prueba para
fn-1 rel fn = Pn-1,n.
La estrategia termina cuando logramos eliminar el hueco. Esto se obtiene cuando logramos tener
EstTrans f f' f' g, por lo que la prueba de f' rel f' es una prueba trivial, representada por
la reflexividad (deberia ser un meta-axioma independiente de las teorias, tal que f rel f).

-}

data EstTrans where
    EstTrans :: Ctx -> Relation -> Focus -> Focus -> 
                Focus -> Focus -> Proof -> Proof -> EstTrans

-- NOTA: no me queda claro como se maneja el contexto en una prueba transitiva
-- nosotros tenemos las 2 pruebas parciales que tienen sus hipotesis. 
-- La prueba resultante, deberia tener las hipotesis de ambas? es decir,
-- si tenemos la prueba Trans cr rel f1 f2 f3 p12 p23, entonces
-- cr = M.union (getCtx p12) (getCtx p23).?
createTransProof :: Ctx -> Relation -> Focus -> Focus -> Focus -> 
                    Proof -> Proof -> Proof
createTransProof ctx rel f1 f2 f3 p12 p23 =
    let new_ctx = M.unions [ctx,(getCtx p12),(getCtx p23)] in
        Trans new_ctx rel f1 f2 f3 p12 p23


{- 
Paso hacia abajo, el valor de retorno es un either, en el cual,
si es left, significa que todavia tenemos un hueco, por lo tanto no terminamos la
prueba.
Si tenemos Right, entonces obtuvimos una prueba completa, sin huecos.
Necesitamos una prueba trivial para probar p=p (reflexividad).
-}
stepDown :: EstTrans -> Focus -> Proof -> Either EstTrans Proof
{-
La prueba que teniamos hasta este momento es:
    fi
rel     {prueba pi1}
    fm1
rel     {hueco}
    fm2
rel     {prueba p2f}
    ff

Queremos agregar un paso a la prueba, desde arriba. El paso es
    fm1
rel    {prueba p}
    f

La prueba resultante es:
     fi
rel     { prueba: Trans fi fm1 f pi1 p }
     f
rel     { hueco }
     fm2
rel     {prueba p2f}
     ff
-}

stepDown (EstTrans ctx rel fi fm1 fm2 ff pi1 p2f) f p = 
{-
Si la expresion nueva es igual a fm2, entonces llenamos el hueco, 
por lo tanto, terminamos la prueba
-}
    let new_proof = createTransProof ctx rel fi fm1 f pi1 p in
        if f==fm2 then
            -- El contexto nuevo se obtiene como union entre new_proof y p2f, por
            -- eso le pasamos M.empty
            Right $ createTransProof M.empty rel fi f ff new_proof p2f
        else
            Left $ EstTrans M.empty rel fi f fm2 ff new_proof p2f


stepUp :: EstTrans -> Focus -> Proof -> Either EstTrans Proof
stepUp (EstTrans ctx rel fi fm1 fm2 ff pi1 p2f) f p = 
    let new_proof = createTransProof ctx rel f fm2 ff p p2f in
        if f==fm1 then
            Right $ createTransProof M.empty rel fi f ff pi1 new_proof
        else
            Left $ EstTrans M.empty rel fi fm1 f ff pi1 new_proof

