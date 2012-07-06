{-# Language OverloadedStrings #-}
module Equ.Theories.Common where

import Equ.Syntax
import Equ.Types
import Equ.Expr
import Equ.PreExpr
import Equ.PreExpr.Symbols(natSucc)
import Equ.Rule
import Equ.Theories.AbsName
import Prelude hiding (and,or)

import qualified Data.Map as M

-- | Constante True
folTrue :: Constant
folTrue = Constant { conRepr = "True"
                   , conName = CTrue
                   , conTy = tyBool
                   }

-- | Constante False  
folFalse :: Constant          
folFalse = Constant { conRepr = "False"
                    , conName = CFalse
                    , conTy = tyBool
                    }
                     


-- | Equivalencia &#8801;
folEquiv :: Operator
folEquiv = Operator { opRepr = "≡"
                    , opName = Equival
                    , opTy = tyBool :-> tyBool :-> tyBool
                    , opAssoc = ALeft
                    , opNotationTy = NInfix
                    , opPrec = 1
                    , opGlyphs = ["=="]
                    }

-- | Igualdad =
folEqual :: Operator
folEqual = Operator { opRepr = "="
                    , opName = Equal
                    , opTy = tyVar "A" :-> tyVar "A" :-> tyBool
                    , opAssoc = ALeft
                    , opNotationTy = NInfix
                    , opPrec = 5
                    , opGlyphs = []
                    }
                    
                    

-- | Conjuncion &#8743;
folAnd :: Operator
folAnd = Operator { opRepr = "∧"
                  , opName = And
                  , opTy = tyBool :-> tyBool :-> tyBool
                  , opAssoc = ALeft
                  , opNotationTy = NInfix
                  , opPrec = 3
                  , opGlyphs = ["&&","/\\"]
                  }

-- | Disyuncion &#8744;
folOr :: Operator
folOr = Operator { opRepr = "∨"
                 , opName = Or
                 , opTy = tyBool :-> tyBool :-> tyBool
                 , opAssoc = ALeft
                 , opNotationTy = NInfix
                 , opPrec = 3
                 , opGlyphs = ["||","\\/"]
                 }


-- | Igualdad
equal :: Expr -> Expr -> Expr
equal (Expr a) (Expr b) = Expr $ BinOp folEqual a b

-- | Constructor de Constantes logicas
true :: Expr
true = Expr $ Con $ folTrue

false :: Expr
false = Expr $ Con $ folFalse

-- | And
and :: Expr -> Expr -> Expr
and (Expr p) (Expr q) = Expr $ BinOp folAnd p q

-- | Or
or :: Expr -> Expr -> Expr
or (Expr p) (Expr q) = Expr $ BinOp folOr p q


-- | Equivalencia
equiv :: Expr -> Expr -> Expr
equiv (Expr p) (Expr q) = Expr $ BinOp folEquiv p q

-- Combinadores para axiomas usuales.
symmetryEquiv :: (Expr -> Expr -> Expr) -> Expr -> Expr -> Expr
symmetryEquiv op e e' = (e `op` e') `equiv` (e' `op` e)

-- | Asociatividad: @(e op e') op e'' = e op (e' op e'')@.
associativityEquiv :: (Expr -> Expr -> Expr) -> Expr -> Expr -> Expr -> Expr 
associativityEquiv op e e' e'' = ((e `op` e') `op` e'') `equiv` (e `op` (e' `op` e''))

-- | Neutro a izquierda: @n op e = e@.
leftNeutralEquiv :: (Expr -> Expr -> Expr) -> Expr -> Expr -> Expr
leftNeutralEquiv op n e = (n `op` e) `equiv` e

-- | Neutro a derecha: @n op e = e@.
rightNeutralEquiv :: (Expr -> Expr -> Expr) -> Expr -> Expr -> Expr
rightNeutralEquiv op n e = (e `op` n) `equiv` e


-- | Simetria: @e op e' = e' op e@.
symmetryEqual :: (Expr -> Expr -> Expr) -> Expr -> Expr -> Expr
symmetryEqual op e e' = (e `op` e') `equal` (e' `op` e)

-- | Asociatividad: @(e op e') op e'' = e op (e' op e'')@.
associativityEqual :: (Expr -> Expr -> Expr) -> Expr -> Expr -> Expr -> Expr 
associativityEqual op e e' e'' = ((e `op` e') `op` e'') `equal` (e `op` (e' `op` e''))



-- | Neutro a izquierda: @n op e = e@.
leftNeutral :: (Expr -> Expr -> Expr) -> Expr -> Expr -> Expr
leftNeutral op n e = (n `op` e) `equal` e

-- | Neutro a derecha: @n op e = e@.
rightNeutral :: (Expr -> Expr -> Expr) -> Expr -> Expr -> Expr
rightNeutral op n e = (e `op` n) `equal` e

-- | 
isTrue :: PreExpr -> Bool
isTrue (Con t) = conName t == CTrue
isTrue _ = False


-- | 
isFalse :: PreExpr -> Bool
isFalse (Con t) = conName t == CFalse
isFalse _ = False


{-| Expresiones para la construcción de axiomas para cuantificadores en general.
    En cada teoria se puede llamar a estas funciones para construir los axiomas
    particulares. -}



-- | Rango Vacío para un cuantificador.
{- Esta funcion crea la expresion para un axioma de rango vacio. Toma una funcion
   que construye la expresion cuantificada, una funcion que crea la relación del cuantificador
   (por ejemplo equiv para el para todo, equal para la sumatoria). una variable, el termino y
   el elemento neutro del cuantificador. La forma general de la regla es:
   < Q v : False : term > rel neuter
   -}
emptyRange :: (Variable -> Expr -> Expr -> Expr) -> (Expr -> Expr -> Expr) ->
              Variable -> Expr -> Expr -> Expr
emptyRange quant rel v term neuter = rel (quant v false term) neuter

-- | Rango Unitario para un cuantificador
{- Esta funcion crea la expresion para un axioma de rango unitario. Toma una funcion
   que construye la expresion cuantificada, una funcion que crea la relación del cuantificador
   (por ejemplo equiv para el para todo, equal para la sumatoria). una variable, una expresion
   y el termino. La forma general de la regla es:
   < Q v : v = e : term > rel term[v:=e] -}
unitRange :: (Variable -> Expr -> Expr -> Expr) -> (Expr -> Expr -> Expr) ->
             Variable -> Expr -> Expr -> Expr
unitRange quant rel v e term = rel (quant v qrange term) (applySubst' term subst)
    where qrange = (Expr $ Var v) `equal` e
          subst = let (Expr pe) = e in
                    M.fromList [(v,pe)]

          
-- Particion de rango.
{- Regla general:
        < Q v : or R S : T > rel < Q v : R : T > oper < Q v : S : T >
-}
partRange :: (Variable -> Expr -> Expr -> Expr) -> (Expr -> Expr -> Expr) ->
             Variable -> Expr -> Expr -> Expr -> Expr
partRange quant rel v r s t =
    rel (quant v (or r s) t) (or (quant v r t) (quant v s t))

    
-- PARTICION DE RANGO GENERALIZADA: Necesito importar el cuantificador existencial.

-- | Regla del término.
{- Forma general:
   < Q v : range : t op g > rel < Q v : range : t > op < Q v : range : g >
   -}
termRule :: (Variable -> Expr -> Expr -> Expr) -> (Expr -> Expr -> Expr) ->
            (Expr -> Expr -> Expr) -> Variable -> Expr -> Expr -> Expr -> Expr
termRule quant rel oper v qrange term1 term2 =
    rel (quant v qrange (oper term1 term2)) (oper (quant v qrange term1)
                                                  (quant v qrange term2))
-- | Regla del término constante
{- Forma general:
   < Q v : range : term > rel term
   Notar que en term no debe ocurrir libremente la variable v. El rango debe ser no vacio.
   Por ultimo el operador debe ser idempotente.
   -}
   
constTermRule :: (Variable -> Expr -> Expr -> Expr) -> (Expr -> Expr -> Expr) ->
                 Variable -> Expr -> Expr -> Expr
constTermRule quant rel v r c = rel (quant v r c) c

-- | Distributividad a izquierda en cuantificadores
{- Puede usarse cuando tenemos un operador que es distributivo a izquierda 
   con respecto al operador cuantificado y se cumple : El rango es no vacío o 
   el elemento neutro del operador cuantificado existe y es absorvente para el otro
   operador (o ambas cosas). Forma general:
   < Q i : range : x oper T >   rel   x oper < Q i : R : T >
   
   -}
distLeftQuant :: (Variable -> Expr -> Expr -> Expr) -> (Expr -> Expr -> Expr) ->
                 (Expr -> Expr -> Expr) -> Variable -> Expr -> Expr -> Expr -> Expr
distLeftQuant quant rel oper v qrange x term =
    rel (quant v qrange (oper x term)) (oper x (quant v qrange term))

    
-- | Distributividad a derecha en cuantificadores
distRightQuant :: (Variable -> Expr -> Expr -> Expr) -> (Expr -> Expr -> Expr) ->
                 (Expr -> Expr -> Expr) -> Variable -> Expr -> Expr -> Expr -> Expr
distRightQuant quant rel oper v qrange x term =
    rel (quant v qrange (oper term x)) (oper (quant v qrange term) x)

    
-- | Regla de Anidado
{- De nuevo acá tenemos condiciones para poder aplicar la regla.
   En los predicados R y S, en R no debe ocurrir una de las variables cuantificadas.
   Forma general:
   < Q v,w : R.v && S.v.w : T.v.w > rel < Q v : R.v : < Q w : S.v.w : T.v.w > >
   
   Notar que la manera que tenemos de representar cuantificaciones dobles es:
   < Q v,w : R : T > equivale a < Q v : True : < Q w : R : T > >
   -}
nestedRule :: (Variable -> Expr -> Expr -> Expr) -> (Expr -> Expr -> Expr) ->
              Variable -> Variable -> Expr -> Expr -> Expr -> Expr
nestedRule quant rel v w r s term =
    rel (quant v true (quant w (and r s) term)) 
        (quant v r (quant w s term))
   
changeVar :: (Variable -> Expr -> Expr -> Expr) -> (Expr -> Expr -> Expr) ->
              Variable -> Variable -> Expr -> Expr -> Expr
changeVar quant rel v w r t =
    rel (quant v r t) (quant w (applySubst' r subst) (applySubst' t subst))
    where subst = M.fromList [(v,Var w)]

-- REGLA DE CAMBIO DE VARIABLE LA TENEMOS GRATIS POR COMO HACEMOS REESCRITURA?? (es una pregunta)

-- | Extensión de applySubst a Expr
applySubst' :: Expr -> ExprSubst -> Expr
applySubst' (Expr p) = Expr . applySubst p
