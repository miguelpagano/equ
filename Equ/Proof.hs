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


import Equ.Proof.Proof
import Equ.Proof.Monad
import Equ.Proof.Error

import Equ.Expr
import Equ.PreExpr
import Equ.Theories
import Equ.Rule
import Equ.Rewrite
import Equ.Theories.FOL

import Equ.Parser

import qualified Data.Text as T
import Data.Map (unions)
import qualified Data.Map as M
import Control.Monad

isRight (Right _) = True
isRight _ = False

firstWithDef :: a -> (a -> Bool) -> [a] -> a
firstWithDef def f xs = head $ filter f xs ++ [def]

firstRight :: Either a b -> [Either a b] -> Either a b
firstRight def = firstWithDef def isRight
                 


{- 
Funciones para construir y manipular pruebas.
Este kit de funciones debería proveer todas las herramientas
necesarias para desarrollar pruebas en equ 
-}

firstProof :: [PM Proof] -> PM Proof
firstProof = firstRight $ Left ProofError

-- Funcion para checkear igualdad, con la variante importante que en caso de
-- no cumplirse devolvemos un resultado por default.
checkEqWithDefault :: Eq a => d -> a -> a -> Either d ()
checkEqWithDefault def a b | a /= b = Left def
                           | otherwise = Right ()

whenEqWithDefault :: Eq a => ProofError -> a -> a -> PM ()
whenEqWithDefault def a b = whenPM (==a) def b >> return ()

{- 
Funciones para construir y manipular pruebas.
Este kit de funciones debería proveer todas las herramientas
necesarias para desarrollar pruebas en equ 
-}



proofFromRule :: Truth t => Focus -> Focus -> Relation -> t -> (t -> Basic) -> 
                            Rule -> PM Proof
proofFromRule f1 f2 rel t mkBasic r = whenEqWithDefault err rel (truthRel t) >>
                                      liftRw (focusedRewrite f1 r) >>= \f ->
                                      whenEqWithDefault err f f2 >>
                                      (Right $ Simple M.empty rel f1 f2 $ mkBasic t)
        where err :: ProofError
              err = BasicNotApplicable $ mkBasic t

-- | Dados dos focuses f1 y f2, una relacion rel y un axioma a, intenta crear una prueba
-- para f1 rel f2, utilizando el paso simple de aplicar el axioma a.
proofFromAxiom :: Focus -> Focus -> Relation -> Axiom -> PM Proof
proofFromAxiom f1 f2 rel a = firstRight err $
                             map (proofFromRule f1 f2 rel a Ax) (truthRules a)
    where err = Left $ BasicNotApplicable $ Ax a

-- | Dados dos focuses f1 y f2, una relacion rel y un teorema t, intenta crear una prueba
-- para f1 rel f2, utilizando el paso simple de aplicar el teorema t.
proofFromTheorem :: Focus -> Focus -> Relation -> Theorem -> PM Proof
proofFromTheorem f1 f2 rel t = firstRight err $ 
                               map (proofFromRule f1 f2 rel t Theo) (truthRules t) 
    where err = Left $ BasicNotApplicable $ Theo t



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

-- Miguel: esto parece muy raro: qué nos garantiza que la prueba p12 sea
-- realmente una prueba de f1 rel f2 (análogo con p23). Esto deberíamos 
-- probarlo; notemos que podemos tomar sólo las dos pruebas como 
-- parámetros (si hacemos eso, entonces tenemos que comprobar que los
-- contextos son iguales, que el final de p12 es igual al principio de 
-- p23 y que las dos relaciones son las mismas. Por otro lado, el contexto
-- de las pruebas debería ser el mismo (no estoy seguro que esté bien 
-- como tenemos ahora a los contextos); la intuición es que los contextos
-- nos dicen qué hipótesis asumimos, por lo tanto en las únicas pruebas
-- que debería cambiar es en las pruebas por casos, inducción y deducción.
mkTransProof :: Ctx -> Relation -> Focus -> Focus -> Focus -> 
                    Proof -> Proof -> Proof
mkTransProof ctx rel f1 f2 f3 p12 p23 = Trans new_ctx rel f1 f2 f3 p12 p23
    where new_ctx = unions [ctx,(getCtx p12),(getCtx p23)]
        


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
    let new_proof = mkTransProof ctx rel fi fm1 f pi1 p in
        if f==fm2 then
            -- El contexto nuevo se obtiene como union entre new_proof y p2f, por
            -- eso le pasamos M.empty
            Right $ mkTransProof M.empty rel fi f ff new_proof p2f
        else
            Left $ EstTrans M.empty rel fi f fm2 ff new_proof p2f


stepUp :: EstTrans -> Focus -> Proof -> Either EstTrans Proof
stepUp (EstTrans ctx rel fi fm1 fm2 ff pi1 p2f) f p = 
    let new_proof = mkTransProof ctx rel f fm2 ff p p2f in
        if f==fm1 then
            Right $ mkTransProof M.empty rel fi f ff pi1 new_proof
        else
            Left $ EstTrans M.empty rel fi fm1 f ff pi1 new_proof

