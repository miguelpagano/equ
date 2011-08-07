-- | Definición de los erores del type-checker.
{-# Language ExistentialQuantification #-} 

module Equ.TypeChecker.Error where
import Equ.Syntax
import Equ.Types

-- | Errores de type-checking.
data TyErr = ErrNotExpected Type Type -- ^ El tipo inferido/obtenido (primer
                                      -- argumento) no es el mismo que el 
                                      -- esperado (segundo argumento).

           -- | Una variable tiene un tipo distinto al asignado por el
           -- contexto.
           | forall s . Syntactic s => ErrClashTypes s [Type]  
           | ErrUnification Type Type [(TyVarName,Type)]

instance Show TyErr where
    show (ErrNotExpected t t') = "[ERR] Expected " ++ show t ++ ", inferred " ++ show t'
    show (ErrClashTypes s ts) = "[ERR] " ++ show (tRepr s) ++ " has more than one type: " ++ show ts
    show (ErrUnification t t' s) = "[ERR] Non-unifiable types: " ++ show t ++ " and " ++ show t' ++ "Subst: " ++ show s