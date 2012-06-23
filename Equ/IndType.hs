module Equ.IndType where

import Equ.Types
import Equ.Syntax
import Equ.PreExpr
import Equ.TypeChecker(unifyTest)

import Data.Text hiding (map)


-- | Un tipo inductivo permite realizar Pattern Matching. Está relacionado con una teoria.
data IndType = IndType {
            name :: Text
          , ty :: Type
          , constants :: [Constant]
          , baseConstructors :: [Operator]
          , indConstructors :: [Operator]
}


-- | Un tipo inductivo valido debe ser construido con la siguiente funcion.
-- | Si es el tipo que se quiere construir, t, es válido devuelve Just t. Otro caso Nothing.
createIndType :: Text -> Type -> [Constant] -> [Operator] -> [Operator] -> Maybe IndType
createIndType name t constants bcons icons = 
    if validConstructors constants bcons icons t
        then Just $ IndType {
                        name = name
                      , ty = t
                      , constants = constants
                      , baseConstructors = bcons
                      , indConstructors = icons
                    }
        else Nothing
                                       
             
validConstructors :: [Constant] -> [Operator] -> [Operator] -> Type -> Bool
validConstructors constants bcons indcons t =
       (and $ map (flip isConstant t) constants) &&
       (and $ map (flip isBaseConstructor t) bcons) &&
       (and $ map (flip isIndConstructor t) indcons)
             
isValidIndType :: IndType -> Bool
isValidIndType it = 
    validConstructors consts bcons icons (ty it)
    
    where bcons = baseConstructors it
          icons = indConstructors it
          consts = constants it
          

isVar :: PreExpr -> Type -> Bool
isVar (Var v) t = unifyTest t (varTy v)
isVar _ _ = False
          
isConstant :: Constant -> Type -> Bool
isConstant c t = unifyTest t (conTy c)
          
isBaseConstructor :: Operator -> Type -> Bool
isBaseConstructor op t = case opTy op of
                            t1 :-> t2 -> unifyTest t t2 && not (typeContains t1 t)
                            otherwise -> False
          
isIndConstructor :: Operator -> Type -> Bool
isIndConstructor op t = case opTy op of
                            t1 :-> t2 -> (unifyTest t t2) && (typeContains t1 t)
                            otherwise -> False
          -- typeContains t t' es true si t es t' o es de tipo funcion y contiene a t', ejemplo:
          -- typeContains (t1 :-> t2 :-> t3) t1 = true
          -- typeContains (t1 :-> t2 :-> t3) t4 = false
          
          
typeContains :: Type -> Type -> Bool
typeContains t t' = case t of
                        t1 :-> t2 -> typeContains t1 t' || typeContains t2 t'
                        t'' -> unifyTest t'' t'
          
isConstantPattern :: PreExpr -> Type -> Bool
isConstantPattern (Con c) t = isConstant c t
isConstantPattern _ _ = False

isBaseConstPattern :: PreExpr -> Type -> Bool
isBaseConstPattern = isConstructorPattern isBaseConstructor

isIndConstPattern :: PreExpr -> Type -> Bool
isIndConstPattern = isConstructorPattern isIndConstructor          
          
isConstructorPattern :: (Operator -> Type -> Bool) -> PreExpr -> Type -> Bool
isConstructorPattern f (UnOp op e) t = f op t && isVar e t
isConstructorPattern f (BinOp op e1 e2) t = f op t && isVar e1 t && isVar e2 t
isConstructorPattern _ _ _ = False

