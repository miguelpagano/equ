-- | Transforma una PreExpresión en una Expresión.
module Equ.TypeChecker 
    ( module Equ.TypeChecker.Error      
      -- * Algoritmo de unificación con relación de orden.
    , unify
    , emptySubst
    , unifyTest
    , rewrite
      -- * Algoritmo de TypeChecking.
    , checkPreExpr
    , freshVars
    )
    where

import Equ.Syntax
import Equ.PreExpr
import Equ.Types
import Equ.Theories.AbsName
import Equ.TypeChecker.Error

import qualified Data.Map as M
import qualified Data.Text as T
import qualified Data.Sequence as S
import Data.Poset (leq)
import Control.Monad.Trans.Either (runEitherT, hoistEither)
import Control.Monad.Trans.Class (lift)
import Control.Monad.RWS.Class (local, ask, tell, get, put)
import Control.Monad.RWS (runRWS)

-- | Tipo de la sustitución para unificar expresiones de tipo.
type TySubst = M.Map TyVarName Type

-- | El error está acompañado de la expresión enfocada donde ocurrió.
type TMErr = (Focus,TyErr)

-- TODO: cambiar: el estado tendría el contexto además de la
-- sustitución.
-- | La mónada de estado del type-checker.
type TyState = MonadTraversal TMErr TySubst

-- | Agrega una línea de log.
addLog :: String -> TyState ()
addLog s = tell . S.fromList $ [T.pack s]

-- | Generación de mensaje de Error.
tyerr :: TyErr -> TyState a
tyerr err = ask >>= \foc -> hoistEither $ Left (foc, err)

{- 

   Las PreExpresiones y las Expresiones son básicamente árboles de
   sintaxis abstracta con distinta información en cada nodo.  Por
   ejemplo, podría ser que las PreExpresiones tengan un componente de
   tipo 'Maybe Type', mientras que el mismo componente en una Expresión
   será de tipo 'Type'. Esto nos permite ver las PreExpresiones cómo
   Expresiones parcialmente tipadas.

   Una cosa que sí necesitamos es información sobre por qué falló un
   chequeo/inferencia de tipos. 

   El type-checker usará en lo posible la información de tipos de las
   PreExpresiones; de esta manera podremos tener un chequeo incremental.

-}

-- | Ciertos símbolos deben tener un único tipo en toda una expresión;
-- un contexto lleva la cuenta de todos los tipos que vamos viendo. En
-- principio sólo debería un tipo a lo sumo.
type CtxSyn s = M.Map s [Type]

-- | El contexto global es un conjunto con los contextos de cada tipo
-- de símbolo; el contexto para los cuantificadores es fijo,
-- inicialmente tiene los cuantificadores "homogéneos" (por ejemplo,
-- sumatoria está, pero forall no está).
data Ctx = Ctx { vars :: CtxSyn VarName
               , funcs :: CtxSyn FuncName
               , ops  :: CtxSyn OpName 
               , cons :: CtxSyn ConName
               , quants :: CtxSyn QuantName
               }


-- | Agrega elementos en la lista de valores.
insertList :: Ord k =>  k -> v -> M.Map k [v] -> M.Map k [v]
insertList k v = M.insertWith (++) k [v] 

-- | Agrega los tipos vistos para una variable al contexto; esta función
-- se usa en el chequeo de tipos de cuantificadores.
addVar :: Ctx -> Variable -> [Type] -> Ctx
addVar c _ [] = c
addVar c v ts = c { vars = M.insert (tRepr v) ts (vars c) }

-- | Devuelve un par con los tipos vistos de una variable y un nuevo
-- contexto sin esa variable.
removeVar :: Ctx -> Variable -> (Ctx,[Type])
removeVar c v = (c { vars = M.delete (tRepr v) (vars c) } , M.findWithDefault [] vn vs)
    where vn = tRepr v
          vs = vars c

-- | Aplicar una sustitución (finita) a un variable de tipo.
findVar :: TyVarName -> TySubst -> Type
findVar v = M.findWithDefault (TyVar v) v

-- | Uso de una sustitución para reemplazar todas las variables en un
-- tipo.
rewrite :: TySubst -> Type -> Type
rewrite s = (>>= (\v -> findVar v s))

-- | Chequeo de diferentes elementos sintácticos simples como
-- variables, constantes, símbolos de función y operadores.
checkSyn :: (Syntactic s,Ord k) => s -> (s -> k) -> (s -> Type) -> 
           (Ctx -> M.Map k [Type], Ctx -> M.Map k [Type] -> Ctx) -> Ctx -> TyState (Ctx,Type)
checkSyn s n t (i,j) ctxs = case M.lookup sName ctx of
                              Nothing -> return $ (j ctxs (insertList sName sTy ctx),sTy)
                              Just ts -> if head ts == sTy
                                        then return (ctxs,sTy)
                                        else tyerr $ ErrClashTypes s (sTy:ts)
    where (sName, sTy) = (n s, t s)
          ctx = i ctxs

-- | Las diferentes instancias de checkSyn.
checkVar,checkFun :: Syntactic s => s -> Ctx -> TyState (Ctx, Type)
checkVar v = checkSyn v tRepr tType (vars, \ctx vctx -> ctx { vars = vctx})
checkFun f = checkSyn f tRepr tType (funcs, \ctx fctx -> ctx { funcs = fctx})
checkCon :: Constant -> Ctx -> TyState (Ctx, Type)
checkCon c = checkSyn c conName tType (cons, \ctx cctx -> ctx { cons = cctx})
checkOp :: Operator -> Ctx -> TyState (Ctx, Type)
checkOp op = checkSyn op opName tType (ops, \ctx octx -> ctx { ops = octx})
checkQuant :: Quantifier -> Ctx -> TyState (Ctx,Type)
checkQuant q = checkSyn q quantName tType (quants, \ctx _ -> ctx)


-- | Algoritmo de unificación. Suponemos que no hay 'TyUnknown'.
unify :: Type -> Type -> TySubst -> Either TyErr TySubst
unify t@(TyAtom _) t'@(TyAtom _) s | t `leq` t' = return s
                                   | otherwise = Left $ ErrUnification t t' (M.toList s)
unify (t :-> t') (r :-> r') s = unify t r s >>= unify t' r'
unify (TyList t) (TyList t') s = unify t t' s
unify t@(TyVar v) t' s | t == t' = return s
                       | v `occurs` t' = Left $ ErrUnification (TyVar v) t' (M.toList s)
                       | v `M.member` s  = unify (M.findWithDefault TyUnknown v s) t' s
                       | otherwise = return . M.insert v t' . M.map ((tyreplace v) t') $ s
unify t (TyVar v) s = unify (TyVar v) t s
unify t t' s = Left $ ErrUnification t t' (M.toList s)

-- | Usamos unify para comprobar si existe o no unificación. 
--   Suponemos que no hay 'TyUnknown'.
unifyTest :: Type -> Type -> Bool
unifyTest t t' = either (const False) (const True) $ unify t t' emptySubst

-- | Sustitución vacía.
emptySubst :: TySubst
emptySubst = M.empty

-- | Generación de variables de tipo frescas.
freshVars :: Type -> [TyVarName]
freshVars t =  filter (not . flip occurs t) [(T.pack . ("t"++) . show) n | n <- [(0::Int)..]]

-- | Actualiza los tipos en el contexto.
updateCtx :: Ctx -> TySubst -> Ctx
updateCtx ctx subst = ctx { vars = M.map (map (rewrite subst)) (vars ctx) 
                          , ops = M.map (map (rewrite subst)) (ops ctx) 
                          , cons = M.map (map (rewrite subst)) (cons ctx) }

-- | Checkea una sub-expresión y actualiza el contexto.
checkAndUpdate :: Ctx -> PreExpr -> (Focus -> Maybe Focus) -> TyState (Ctx,Type)
checkAndUpdate ctx e go = localGo go (check ctx e) >>= \(ctx',t) ->
                          get >>= \s -> 
                          return (updateCtx ctx' s,t)


-- TODO: 
--  * agregar el contexto al estado?
--  * extraer la expresión del focus que tenemos en el ambiente?
--  * pensar el caso de cuantificadores; 
--  * definir propiedades.
check :: Ctx -> PreExpr -> TyState (Ctx,Type)
check ctx (Var v) = checkVar v ctx
check ctx (Con c) = checkCon c ctx
check ctx (Fun f) = checkFun f ctx                           
check ctx (PrExHole h) = return (ctx,tType h)
check ctx (Paren e) = localGo goDown (check ctx e)
check ctx (UnOp op e) = do (ctx', t) <- checkAndUpdate ctx e goDown
                           addLog $ "Operando OK: " ++ show t
                           (ctx'', t') <- checkOp op ctx'
                           addLog $ "Operador" ++ show op ++ " OK: " ++ show t'
                           s <- get 
                           w <- return . head . filter (not . (`elem` (M.keys s))) $ freshVars (t :-> t')
                           case unify t' (t :-> TyVar w) s of
                             Left err -> addLog (show (t,t',w)) >> tyerr err
                             Right s' -> put s' >> (lift . return) (ctx'', findVar w s')
check ctx (BinOp op e e') = do (ctx', te) <- checkAndUpdate ctx e goDown
                               addLog $ "Operando izquierda OK: " ++ show te
                               (ctx'', te') <- checkAndUpdate ctx' e' goDownR
                               addLog $ "Operando derecha OK: " ++ show te'
                               (ctx''', tOp) <- checkOp op ctx''
                               addLog $ "Operador " ++ show op ++" OK: " ++ show tOp
                               s <- get
                               w <- return . head . filter (not . (`elem` (M.keys s))) $ freshVars (te :-> te' :-> tOp)
                               case unify (te :-> te' :-> TyVar w) tOp s of
                                 Left err -> addLog (show w) >> tyerr err
                                 Right s'  -> put s' >> (lift . return) (ctx''', findVar w s')
check ctx (App e e') = do (ctx', te) <- checkAndUpdate ctx e goDown
                          addLog "Funcion OK"
                          (ctx'', te') <- checkAndUpdate ctx' e' goDownR
                          addLog "Argumento OK"
                          s <- get
                          w <- return . head . filter (not . (`elem` (M.keys s))) $ freshVars (te :-> te')
                          case unify te (te' :-> TyVar w) s of 
                            Left err -> tyerr err
                            Right s' -> put s' >> (lift . return) (ctx'', findVar w s')
check ctx (Quant q v r t) = do (_, tyQ) <- checkQuant q ctx
                               addLog "Cuantificador OK"
                               (ctx', tysV) <- lift . return $ removeVar ctx v
                               (ctxV, tyV) <- checkAndUpdate ctx' (Var v) Just
                               addLog "Variable OK"
                               (ctxR, tyR) <- checkAndUpdate ctxV r goDown
                               addLog "Rango OK"
                               (ctxT, tyT) <- checkAndUpdate ctxR t goDownR
                               addLog "Termino OK"
                               case tyQ of 
                                 t1 :-> t2 -> case (tyV `leq` t1, t2 `leq` tyT, tyR == tyBool) of
                                               (False,_,_) -> tyerr $ ErrNotExpected t1 tyV
                                               (_,False,_) -> tyerr $ ErrNotExpected tyBool tyR
                                               (_,_,False) -> tyerr $ ErrNotExpected t2 tyT
                                               (True,True,True) -> return (addVar ctxT v tysV, tyT)
                                 t1 -> tyerr $ ErrNotExpected (tyV :-> tyT) t1


initCtx :: Ctx
initCtx = Ctx { vars = M.empty
              , funcs = M.empty
              , ops  = M.empty
              , cons = M.empty
              , quants = M.empty
              }

checkPreExpr :: PreExpr -> Either (TMErr,Log) Type
checkPreExpr e = case runRWS (runEitherT (check initCtx e)) (toFocus e) emptySubst of
                   (res, _, l) -> either (\err -> Left (err,l)) (Right . snd) res
