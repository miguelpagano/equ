-- | Transforma una PreExpresión en una Expresión.
module Equ.TypeChecker 
    ( module Equ.TypeChecker.Error
      -- * Algoritmo de unificación con relación de orden.
    , unify
    , rewrite
    , prop_unify
      -- * Algoritmo de TypeChecking.
    , check
    )
    where
import Equ.Syntax
import Equ.PreExpr
import Equ.Expr
import Equ.Types
import Equ.Theories.AbsName
import Equ.TypeChecker.Error
-- import Equ.ArbitraryPreExpr

import qualified Data.Map as M
import qualified Data.Text as T
import Data.Poset
import Control.Monad.State

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

-- | Tipo de la sustitución para unificar expresiones de tipo.
type TySubst = M.Map TyVarName Type

-- TODO: cambiar la mónada de chequeo de tipos; debería ser un mónada
-- de error dentro de una mónada de estado: el estado tendría el foco
-- y el contexto.
type TyMonad = Either (Path,TyErr)

type TyState a = StateT TySubst TyMonad a

tyerr :: Path -> TyErr -> TyMonad a
tyerr p t = Left (p,t)

-- | Chequeo de diferentes elementos sintácticos simples como
-- variables, constantes, símbolos de función y operadores.
checkSyn :: (Syntactic s,Ord k) => s -> (s -> k) -> (s -> Type) -> (Ctx -> M.Map k [Type], Ctx -> M.Map k [Type] -> Ctx) -> Ctx -> TyMonad (Ctx,Type)
checkSyn s n t (i,j) ctxs = case M.lookup sName ctx of
                              Nothing -> return $ (j ctxs (insertList sName sTy ctx),sTy)
                              Just ts -> if head ts == sTy
                                        then return (ctxs,sTy)
                                        else tyerr Top $ ErrClashTypes s (sTy:ts)
    where (sName, sTy) = (n s, t s)
          ctx = i ctxs

-- Las diferentes instancias de checkSyn.
checkVar v = checkSyn v tRepr tType (vars, \ctx vctx -> ctx { vars = vctx})
checkCon c = checkSyn c conName tType (cons, \ctx cctx -> ctx { cons = cctx})
checkFun f = checkSyn f tRepr tType (funcs, \ctx fctx -> ctx { funcs = fctx})
checkOp op = checkSyn op opName tType (ops, \ctx octx -> ctx { ops = octx})
checkQuant q = checkSyn q quantName tType (quants, \ctx _ -> ctx)


-- | Algoritmo de unificación. Suponemos que no hay 'TyUnknown'.
unify :: Type -> Type -> TySubst -> Either TyErr TySubst
unify t@(TyAtom a) t'@(TyAtom a') s | t `leq` t' = return s
                                    | otherwise = Left $ ErrUnification t t'
unify (t :-> t') (r :-> r') s = unify r t s >>= unify t' r'
unify (TyList t) (TyList t') s = unify t t' s
unify (TyVar v) (TyVar w) s | v == w = return s
                            | v `M.member` s = unify (M.findWithDefault TyUnknown v s) (TyVar w) s
                            | otherwise = return . M.insert v (TyVar w) . M.map (tyreplace v (TyVar w)) $ s
unify (TyVar v) t s | v `occurs` t = Left $ ErrUnification (TyVar v) t
                    | v `M.member` s  = unify (M.findWithDefault TyUnknown v s) t s
                    | otherwise = return . M.insert v t . M.map (flip (tyreplace v) t) $ s
unify t (TyVar v) s = unify (TyVar v) t s
unify t t' _ = Left $ ErrUnification t t'

-- | Uso de una sustitución para reemplazar todas las variables en un
-- tipo.
rewrite :: Type -> TySubst -> Type
rewrite (TyAtom t) s = TyAtom t
rewrite (TyVar v) s = M.findWithDefault (TyVar v) v s
rewrite (TyList t) s = TyList $ rewrite t s
rewrite (t :-> t') s = rewrite t s :-> rewrite t' s
rewrite TyUnknown _ = TyUnknown


-- | Si la unificación fue exitosa, entonces los tipos son iguales después
-- de aplicar la sustitución.
prop_unify :: (Type,Type) -> Bool
prop_unify (t,t') = case unify t t' (M.fromList []) of
                      Left _ -> True
                      Right s -> rewrite t s == rewrite t' s


-- | Generación de variables de tipo frescas.
freshVars :: Type -> [TyVarName]
freshVars t =  filter (not . flip occurs t) [(T.pack . ("t"++) . show) n | n <- [0..]]


-- | Si v in freshVars t, entonces no (occurs v t).
prop_freshVars :: Type -> Bool
prop_freshVars t = and . take 2 . map (not . flip occurs t) . freshVars $ t

-- TODO: 
--  * pensar el caso de cuantificadores; 
--  * hacer manejo correcto de errores (ahora son todos errores de
--    unificación sin información del lugar);
--  * definir propiedades.
check :: Ctx -> PreExpr -> TyState (Ctx,Type)
check ctx (Var v) = lift $ either (uncurry tyerr) return $ checkVar v ctx
check ctx (Con c) = lift $ either (uncurry tyerr) return $ checkCon c ctx
check ctx (Fun f) = lift $ either (uncurry tyerr) return $ checkFun f ctx                           
check ctx (PrExHole h) = lift $ return (ctx,tType h)
check ctx (UnOp op e) = do (ctx', t) <- check ctx e
                           (ctx'', t') <- lift (checkOp op  ctx')
                           s <- get 
                           w <- return . TyVar . head $ freshVars (t :-> t')
                           case unify t' (t :-> w) s of
                             Left err -> lift $ tyerr Top err
                             Right s' -> put s' >> (lift . return) (ctx'',rewrite w s')
check ctx (BinOp op e e') = do (ctx', te) <- check ctx e
                               (ctx'', te') <- check ctx' e'
                               (ctx''', tOp) <- lift $ checkOp op ctx''
                               s <- get
                               w <- return . TyVar . head $ freshVars (te :-> te' :-> tOp)                               
                               case unify tOp (te :-> te' :-> w) s of
                                 Left err -> lift $ tyerr Top err
                                 Right s'  -> put s' >> (lift . return) (ctx''',rewrite w s')
check ctx (App e e') = do (ctx', te) <- check ctx e
                          (ctx'', te') <- check ctx' e'
                          s <- get
                          w <- return . TyVar . head $ freshVars (te :-> te')
                          case unify te (te' :-> w) s of 
                            Left err -> lift $ tyerr Top err
                            Right s' -> put s' >> (lift . return) (ctx'', rewrite w s')
check ctx (Paren e) = check ctx e
check ctx (Quant q v r t) = do (_, tyQ) <- lift $ checkQuant q ctx
                               (ctx', tysV) <- lift . return $ removeVar ctx v
                               (ctxV, tyV) <- check ctx' (Var v)
                               (ctxR, tyR) <- check ctxV r
                               (ctxT, tyT) <- check ctxR t
                               case tyQ of 
                                 t1 :-> t2 -> case (tyV `leq` t1, t2 `leq` tyT, tyR == tyBool) of
                                               (False,_,_) -> lift $ tyerr Top (ErrNotExpected t1 tyV)
                                               (_,False,_) -> lift $ tyerr (QuantL q v Top t) (ErrNotExpected tyBool tyR)
                                               (_,_,False) -> lift $ tyerr (QuantR q v r Top) (ErrNotExpected t2 tyT)
                                               (True,True,True) -> lift $ return (addVar ctxT v tysV, tyT)
                                 t1 -> lift $ tyerr Top $ ErrNotExpected (tyV :-> tyT) t1


initCtx :: Ctx
initCtx = Ctx { vars = M.empty
              , funcs = M.empty
              , ops  = M.empty
              , cons = M.empty
              , quants = M.empty
              }
