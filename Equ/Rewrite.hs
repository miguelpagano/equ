module Equ.Rewrite
    ( exprRewrite
    , focusedRewrite
    )
    where

import Equ.Matching
import Equ.Rule
import Equ.Expr
import Equ.PreExpr
import Equ.Syntax
import Equ.TypeChecker

import Data.Map

type RewriteError = MatchError

data TypedRewriteError = UnifyError

{- | Dada una expresi贸n y una regla, si la expresi贸n matchea con el lado
izquierdo de la regla, entonces se reescribe de acuerdo al lado derecho
de la regla.
-}
exprRewrite :: Expr -> Rule -> Either RewriteError Expr
exprRewrite (Expr e) (Rule{lhs=Expr l,rhs=Expr r}) = match l e >>= 
                                                    return . Expr . applySubst r

-- | Igual a exprRewrite pero ademas retorna la lista de sustituciones.
rewriteInformative :: Expr -> Rule -> Either RewriteError (Expr, ExprSubst)
rewriteInformative (Expr e) (Rule{lhs=Expr l,rhs=Expr r}) = 
                                    match l e >>= 
                                    \s -> return (Expr $ applySubst r s, s)

-- | Dado un focus y una regla, aplicamos re-escrituda con la regla a la 
--  expresión focalizada, en caso de exito reemplazamos la expresión inicial
--  por la expresión resultante dentro del focus.
focusedRewrite :: Focus -> Rule -> Either RewriteError Focus
focusedRewrite f@(pe, p) r = exprRewrite (Expr pe) r >>= 
                             \(Expr pe')-> return $ replace f pe'

{- 
    Me di cuenta que no termino de entender que debería hacer esta función.
    Por ejemplo, si hacemos checkPreExpr (parser "0+0") obetenemos
    Right (TyAtom ATyNat) y hasta acá todo bien, hacemos lo mismo para el
    lado izq de la regla. Ahora, con esta substitución que obtengo debería
    cambiar el tipo de 0+0, pero la preExpresion 0+0 no tiene ningun tipo
    asociado fijo que pueda cambiar.
    Sera cambiar el tipo "final", siguiendo con el ejemplo anterior
    tType + = TyAtom ATyNat :-> (TyAtom ATyNat :-> TyAtom ATyNat)
    la idea es cambiar el tipo y que quede;
    tType + = TyAtom ATyNat :-> (TyAtom ATyNat :-> TIPO_NUEVO)
    Me acabo de dar cuenta que solamente se aplicaría a variables de tipo,
    pero bueno aun así me parece que el ejemplo puede ayudar a entender sobre
    lo que dudo.
    
    Dejo escrita la función (con casos incompletos) para ejemplificar lo que
    entiendo. No la termino porque muy probablemente este mal :P
-}
typedRewrite :: Expr -> Rule -> Either TypedRewriteError Expr
typedRewrite (Expr pe) (Rule{lhs=Expr l,rhs=Expr r}) = 
    let (Right te) = checkPreExpr pe
        (Right tr) = checkPreExpr l
    in case unify te tr emptySubst of
        Left _ -> Left UnifyError
        Right ts -> Right $ Expr $ tyRewrite ts pe
    where
        tyRewrite ts (BinOp op pe pe') = 
            BinOp op{opTy = rewrite ts (tType op)} pe pe'
