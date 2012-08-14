{-# Language DoAndIfThenElse,OverloadedStrings #-}
{-| Algoritmo de chequeo e inferencia de tipos para pre-expre-
siones. Este algoritmo es esencialmente el de Hindley-Milner-Damas
para el cálculo lambda: si tenemos informacion en la pre-expresion
entonces se verifica que sea unificable con el tipo de inferido. A
diferencia de esos algoritmos, no se hay un contexto donde se declara
el tipo de las variabes, ya que la informacion de las variables
(símbolos de función y constantes son tratadas exactamente de la misma
manera) está contenida en la expresión misma (en este aspecto se
parece más al chequeo de un cálculo à la Church).
-}
module Equ.TypeChecker 
    ( module Equ.TypeChecker.Error      
      -- * Algoritmo de unificaci&#243;n con relaci&#243;n de orden.
    , unify
    , emptySubst
    , unifyTest
    , unificate
    , rewrite
    , typeCheckPreExpr 
    , typeCheckPre
    , vars
    , cons
    , match
    , match2
      -- * Algoritmo de TypeChecking.
    , checkPreExpr
    , getType
    )
    where

import Equ.Syntax
import Equ.PreExpr
import Equ.Types
import Equ.Theories.AbsName
import Equ.TypeChecker.Error
import Equ.TypeChecker.Unification

import qualified Data.Map as M
import qualified Data.Text as T
import qualified Data.Sequence as S
import qualified Data.Foldable as F
import Data.Poset (leq)
import qualified Data.Set as Set (elems)
import Control.Monad.Trans.Either (runEitherT, hoistEither)
import Control.Monad.Trans.Class (lift)
import Control.Monad.RWS.Class (ask, tell, get, put,gets,modify)
import Control.Monad.RWS (runRWS)

import Control.Applicative((<$>))

-- | Ciertos s&#237;mbolos deben tener un &#250;nico tipo en toda una expresi&#243;n;
-- un contexto lleva la cuenta de todos los tipos que vamos viendo. En
-- principio s&#243;lo deber&#237;a un tipo a lo sumo.
type CtxSyn s = M.Map s [Type]
    
-- | El contexto global es un conjunto con los contextos de cada tipo
-- de s&#237;mbolo; el contexto para los cuantificadores es fijo,
-- inicialmente tiene los cuantificadores "homog&#233;neos" (por ejemplo,
-- sumatoria est&#225;, pero forall no est&#225;).
data Ctx = Ctx { vars :: CtxSyn VarName
               , ops  :: CtxSyn OpName 
               , cons :: CtxSyn ConName
               , quants :: CtxSyn QuantName
               }
         deriving Show

-- | El error est&#225; acompa&#241;ado de la expresi&#243;n enfocada donde ocurri&#243;.
type TMErr = (Focus,TyErr)

-- TODO: cambiar: el estado tendr&#237;a el contexto adem&#225;s de la
-- sustituci&#243;n.
-- | La m&#243;nada de estado del type-checker.
type TyState = MonadTraversal TMErr TCState

data TCState = TCState { subst :: TySubst
                       , ctx   :: Ctx
                       , fTyVar :: Int
                       }
             deriving Show

-- | Agrega una l&#237;nea de log.
addLog :: String -> TyState ()
addLog = tell . S.fromList . return . T.pack 

-- | Generaci&#243;n de mensaje de Error.
tyerr :: TyErr -> TyState a
tyerr err = ask >>= \foc -> hoistEither $ Left (foc, err)

getSub :: TyState TySubst
getSub = gets subst

getCtx :: TyState Ctx
getCtx = gets ctx

getFreshTyVar :: TyState Type
getFreshTyVar = gets fTyVar >>= \n -> 
                modify (\st -> st { fTyVar = n+1}) >>
                return (TyVar $ T.pack (show n))

modCtx :: (Ctx -> Ctx) -> TyState ()
modCtx f = modify (\st -> st { ctx = f (ctx st)})

modSubst :: (TySubst -> TySubst) -> TyState ()
modSubst f = modify (\st -> st { subst = f (subst st)}) >> getSub >>= updateCtxS

{- 

   Las PreExpresiones y las Expresiones son b&#225;sicamente &#225;rboles de
   sintaxis abstracta con distinta informaci&#243;n en cada nodo.  Por
   ejemplo, podr&#237;a ser que las PreExpresiones tengan un componente de
   tipo 'Maybe Type', mientras que el mismo componente en una Expresi&#243;n
   ser&#225; de tipo 'Type'. Esto nos permite ver las PreExpresiones c&#243;mo
   Expresiones parcialmente tipadas.

   Una cosa que s&#237; necesitamos es informaci&#243;n sobre por qu&#233; fall&#243; un
   chequeo/inferencia de tipos. 

   El type-checker usar&#225; en lo posible la informaci&#243;n de tipos de las
   PreExpresiones; de esta manera podremos tener un chequeo incremental.

-}

extCtx :: (Syntactic s,Ord k) => (s -> k) -> s -> [Type] -> CtxSyn k -> CtxSyn k
extCtx f s = M.insertWith (flip const) (f s)

extCtxV :: Variable -> Type -> TyState ()
extCtxV v t = modCtx (\ctx -> ctx { vars = extCtx varName v [t] (vars ctx)})

extCtxOp :: Operator -> Type -> TyState ()
extCtxOp o t = modCtx (\ctx -> ctx { ops = extCtx opName o [t] (ops ctx)})

extCtxCon :: Constant -> Type -> TyState ()
extCtxCon c t = modCtx (\ctx -> ctx { cons = extCtx conName c [t] (cons ctx)})

-- | Agrega los tipos vistos para una variable al contexto; esta funci&#243;n
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

-- | Chequeo de diferentes elementos sint&#225;cticos simples como
-- variables, constantes, s&#237;mbolos de funci&#243;n y operadores.
checkSyn :: (Syntactic s,Ord k) => s -> (s -> k) -> (Ctx -> M.Map k [Type]) -> TyState Type
checkSyn s name getM = gets (getM . ctx) >>= \ctx ->
                       case M.lookup (name s) ctx of
                         Nothing -> tyerr $ ErrClashTypes s []
                         Just ts -> rewriteS (head ts)

-- | Las diferentes instancias de checkSyn.
checkVar :: Syntactic s => s -> TyState Type
checkVar v = checkSyn v tRepr vars
checkCon :: Constant -> TyState Type
checkCon c = checkSyn c conName  cons
checkOp :: Operator -> TyState Type
checkOp op = checkSyn op opName ops
checkQuant :: Quantifier -> TyState Type
checkQuant q = checkSyn q quantName quants

-- | Actualiza los tipos en el contexto.
updateCtx :: Ctx -> TySubst -> Ctx
updateCtx ctx subst = ctx { vars = M.map (map (rewrite subst)) (vars ctx) 
                          , ops = M.map (map (rewrite subst)) (ops ctx) 
                          , cons = M.map (map (rewrite subst)) (cons ctx) }

-- | Checkea una sub-expresi&#243;n y actualiza el contexto.
checkAndUpdate :: PreExpr -> (Focus -> Maybe Focus) -> TyState Type
checkAndUpdate e go = localGo go (check e)

updateCtxS :: TySubst -> TyState ()
updateCtxS = modCtx . flip updateCtx

-- Lifting de unificación para la mónada de TC
unifyS :: Type -> Type -> TyState TySubst
unifyS t t' = getSub >>= \s ->
              case unify t t' s of
                Left err -> addLog ("Error trying to unify: "
                                   ++ show t ++ " and " ++ show t'
                                  )
                           >> tyerr err
                Right s' -> modSubst (const s') >> return s'                

unifyListS [] = getSub
unifyListS [t] = getSub
unifyListS (t:t':ts) = unifyS t t' >> unifyListS (t':ts)

rewriteS :: Type -> TyState Type
rewriteS t = flip rewrite t <$> getSub

-- TODO: 
--  * extraer la expresi&#243;n del focus que tenemos en el ambiente?
--  * pensar el caso de cuantificadores; 
--  * definir propiedades.
check :: PreExpr -> TyState Type
check (Var v) = checkVar v
check (Con c) = checkCon c 
check (PrExHole h) = return (tType h)
check (Paren e) = localGo goDown $ check e
check (UnOp op e) = do t <- checkAndUpdate e goDown
                       t' <- checkOp op
                       w <- getFreshTyVar 
                       unifyS t' (t :-> w) 
                       rewriteS w
check (BinOp op e e') = do te <- checkAndUpdate e goDown
                           te' <- checkAndUpdate e' goDownR
                           tOp <- checkOp op
                           w <- getFreshTyVar
                           unifyS (te :-> te' :-> w) tOp
                           rewriteS w
check (App e e') = do te <- checkAndUpdate e goDown
                      te' <- checkAndUpdate e' goDownR
                      w <- getFreshTyVar
                      unifyS  te (te' :-> w) 
                      rewriteS w
check (Quant q v r t) = do tyQ <- checkQuant q
                           ctx <- getCtx 
                           (ctx',tysV) <- lift . return $ removeVar ctx v
                           modCtx (const ctx')
                           tyV <- checkAndUpdate (Var v) Just
                           tyR <- checkAndUpdate r goDown
                           tyT <- checkAndUpdate t goDownR
                           case tyQ of 
                             t1 :-> t2 -> case (tyV `leq` t1, t2 `leq` tyT, tyR == tyBool) of
                                           (False,_,_) -> tyerr $ ErrNotExpected t1 tyV
                                           (_,False,_) -> tyerr $ ErrNotExpected tyBool tyR
                                           (_,_,False) -> tyerr $ ErrNotExpected t2 tyT
                                           (True,True,True) -> modCtx (\ctx -> addVar ctx v tysV) >>
                                                              return tyT
                             t1 -> tyerr $ ErrNotExpected (tyV :-> tyT) t1
check (If b t f) = do tb <- checkAndUpdate b goDown
                      unifyS tb  (TyAtom ATyBool)
                      tt <- checkAndUpdate t goIfTrue
                      tf <- checkAndUpdate f goIfFalse
                      addLog (show tt ++ show tf)
                      unifyS tt tf
                      rewriteS tt
                                     
check (Case e cs) = do texp <- checkAndUpdate e goDown
                       pats <- mapM checkCase cs
                       unifyListS (texp:map fst pats)
                       unifyListS (map snd pats) 
                       rewriteS (snd (head pats))


-- | Devuelve el tipo de un patrón y de la expresión.
checkCase :: (PreExpr,PreExpr) -> TyState ((Type,Type))
checkCase (pat,exp) = do tpat <- checkPat pat
                         texp <- check exp
                         return (tpat,texp)


checkPat :: PreExpr -> TyState Type
checkPat (Var v) = getFreshTyVar >>= \w -> extCtxV v w >> return w
checkPat (Con c) = checkCon c
checkPat (UnOp op e) = checkOp op >>= \t ->
                       checkPat e >>= \t'->
                       getFreshTyVar >>= \w ->
                       unifyS t (t' :-> w) >>
                       rewriteS w
checkPat (BinOp op e e') = checkOp op >>= \t ->
                           checkPat e >>= \t' ->
                           checkPat e' >>= \t'' ->
                           getFreshTyVar >>= \w ->
                           unifyS t (t' :-> t'' :-> w) >>
                           rewriteS w
checkPat (Paren p) = checkPat p
checkPat _ = error "Expression is not a pattern."

initCtx :: Ctx
initCtx = Ctx { vars = M.empty
              , ops  = M.empty
              , cons = M.empty
              , quants = M.empty
              }

check' e = initCtxE e >> check e

initTCState = TCState { subst = emptySubst
                      , ctx = initCtx
                      , fTyVar = 0
                      }

-- | Construye un contexto con variables frescas para las variables
-- que no tienen un tipo 
mkCtxVar :: PreExpr -> TyState ()
mkCtxVar e = mapM_ updCtx vs
    where vs = Set.elems $ freeVars e
          updCtx v = renTy M.empty (varTy v) >>= extCtxV v . fst

mkCtxOps :: PreExpr -> TyState ()
mkCtxOps = mapM_ updCtx . getOperators
    where updCtx op = renTy M.empty (opTy op) >>= extCtxOp op . fst

mkCtxCon :: PreExpr -> TyState ()
mkCtxCon = mapM_ updCtx . getConstants
    where updCtx con = renTy M.empty (conTy con) >>= extCtxCon con . fst

-- | Dado un tipo, reemplaza todas las variables libres del
-- tipo por variables frescas.
renTy :: TySubst -> Type -> TyState (Type,TySubst)
renTy s TyUnknown = getFreshTyVar >>= \t -> return (t,s)
renTy s t@(TyAtom _) = return (t,s)
renTy s (TyVar v) = maybe newVar (\t -> return (t,s)) $ M.lookup v s
    where newVar = getFreshTyVar >>= \w ->
                   return (w, M.insert v w s)
renTy s (TyList t) = renTy s t >>= \(t',s') -> return (TyList t',s')
renTy s (t :-> t') = renTy s t >>= \(t1,s') -> 
                     renTy s' t' >>= \(t2,s'') -> return (t1 :-> t2,s'')

-- | Genera variables de tipos únicos para operadores, constantes y cuantificadores.
renTyVar :: (s -> Type) -> (s -> Type -> s) -> s -> TyState s
renTyVar get upd s = renTy M.empty (get s) >>= return . upd s . fst

renTyCon = renTyVar conTy (\c t -> c {conTy = t})
renTyOp = renTyVar opTy  (\o t -> o {opTy = t})

initCtxE :: PreExpr -> TyState ()
initCtxE e = mkCtxVar e >> mkCtxOps e >> mkCtxCon e

mkSubst :: Ctx -> ((Variable -> Type), (Constant -> Type), (Operator -> Type))
mkSubst (Ctx vars ops cons _) = (updVar,updCons,updOps)
    where updVar = M.foldrWithKey (\vname ty f var -> if varName var == vname then head ty else f var) tyUnk vars
          updCons = M.foldrWithKey (\cname ty f con -> if conName con == cname then head ty else f con) tyUnk cons
          updOps =  M.foldrWithKey (\opname ty f op -> if opName op == opname then head ty else f op) tyUnk ops
          tyUnk _ = TyUnknown

setType' :: Ctx -> PreExpr -> PreExpr
setType' ctx e = let (v,c,o) = mkSubst ctx
                 in setType v c o e



-- | Retorna el tipo de una expresi&#243;n bien tipada.
checkPreExpr :: PreExpr -> Either (TMErr,Log) Type
checkPreExpr e = case runRWS (runEitherT (check' e)) (toFocus e) initTCState of
                   (res, _, l) -> either (\err -> Left (err,l)) Right res

typeCheckPreExpr :: PreExpr -> Either (TMErr,Log) PreExpr
typeCheckPreExpr e = case runRWS (runEitherT (check' e)) (toFocus e) initTCState of
                   (res, st, l) -> either (\err -> Left (err,l)) (const $ Right $ setType' (ctx st) e) res
-- typeCheckPre :: PreExpr -> Either (TMErr,Log) PreExpr
typeCheckPre e = case runRWS (runEitherT (check' e)) (toFocus e) initTCState of
                   (res, st, l) -> l


getType :: PreExpr -> Maybe Type
getType = either (const Nothing) return . checkPreExpr
