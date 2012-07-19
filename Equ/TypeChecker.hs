
{-# Language DoAndIfThenElse #-}
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
      -- * Algoritmo de TypeChecking.
    , checkPreExpr
    , freshVars
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
import Control.Monad.Trans.Either (runEitherT, hoistEither)
import Control.Monad.Trans.Class (lift)
import Control.Monad.RWS.Class (ask, tell, get, put,gets,modify)
import Control.Monad.RWS (runRWS)

import Control.Arrow(first,second)
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


-- | El error est&#225; acompa&#241;ado de la expresi&#243;n enfocada donde ocurri&#243;.
type TMErr = (Focus,TyErr)

-- TODO: cambiar: el estado tendr&#237;a el contexto adem&#225;s de la
-- sustituci&#243;n.
-- | La m&#243;nada de estado del type-checker.
type TyState = MonadTraversal TMErr (TySubst,Ctx)

-- | Agrega una l&#237;nea de log.
addLog :: String -> TyState ()
addLog = tell . S.fromList . return . T.pack 

-- | Generaci&#243;n de mensaje de Error.
tyerr :: TyErr -> TyState a
tyerr err = ask >>= \foc -> hoistEither $ Left (foc, err)

getSub :: TyState TySubst
getSub = gets fst

getCtx :: TyState Ctx
getCtx = gets snd

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


-- | Agrega elementos en la lista de valores.
insertList :: Ord k =>  k -> v -> M.Map k [v] -> M.Map k [v]
insertList k v = M.insertWith (++) k [v] 

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
checkSyn :: (Syntactic s,Ord k) => s -> (s -> k) -> (s -> Type) -> 
           (Ctx -> M.Map k [Type], Ctx -> M.Map k [Type] -> Ctx) -> TyState Type
checkSyn s n t (i,j) = gets (i . snd) >>= \ctx ->
                       case M.lookup sName ctx of
                         Nothing -> modify (second (flip j (insertList sName sTy ctx))) >>
                                   return sTy
                         Just ts -> getSub >>= \sub ->
                                   case unify (head ts) sTy sub of
                                     Left err -> tyerr $ ErrClashTypes s (sTy:ts)
                                     Right sub' -> return $ rewrite sub' sTy
    where (sName, sTy) = (n s, t s)

-- | Las diferentes instancias de checkSyn.
checkVar :: Syntactic s => s -> TyState Type
checkVar v = checkSyn v tRepr tType (vars, \ctx vctx -> ctx { vars = vctx})
checkCon :: Constant -> TyState Type
checkCon c = checkSyn c conName tType (cons, \ctx cctx -> ctx { cons = cctx})
checkOp :: Operator -> TyState Type
checkOp op = checkSyn op opName tType (ops, \ctx octx -> ctx { ops = octx})
checkQuant :: Quantifier -> TyState Type
checkQuant q = checkSyn q quantName tType (quants, \ctx _ -> ctx)


-- | Generaci&#243;n de variables de tipo frescas.
freshVars :: Type -> [TyVarName]
freshVars t =  filter (not . flip occurs t) [(T.pack . ("t"++) . show) n | n <- [(0::Int)..]]

newTyVar :: TySubst -> Type -> TyVarName
newTyVar s = head . filter (not . (`elem` (M.keys s))) . freshVars 

-- | Actualiza los tipos en el contexto.
updateCtx :: Ctx -> TySubst -> Ctx
updateCtx ctx subst = ctx { vars = M.map (map (rewrite subst)) (vars ctx) 
                          , ops = M.map (map (rewrite subst)) (ops ctx) 
                          , cons = M.map (map (rewrite subst)) (cons ctx) }

-- | Checkea una sub-expresi&#243;n y actualiza el contexto.
checkAndUpdate :: PreExpr -> (Focus -> Maybe Focus) -> TyState Type
checkAndUpdate e go = localGo go (check e) >>= \t ->
                      getSub >>= 
                      modify . second . flip updateCtx >>
                      return t

updateCtxS :: TySubst -> TyState ()
updateCtxS s = modify (second (flip updateCtx s))

-- TODO: 
--  * agregar el contexto al estado?
--  * extraer la expresi&#243;n del focus que tenemos en el ambiente?
--  * pensar el caso de cuantificadores; 
--  * definir propiedades.
check :: PreExpr -> TyState Type
check (Var v) = checkVar v
check (Con c) = checkCon c 
check (PrExHole h) = return (tType h)
check (Paren e) = localGo goDown $ check e
check (UnOp op e) = do t <- checkAndUpdate e goDown
                       addLog $ "Operando OK: " ++ show t
                       t' <- checkOp op
                       addLog $ "Operador" ++ show op ++ " OK: " ++ show t'
                       s <- getSub
                       w <- return $ newTyVar s (t :-> t')
                       case unify t' (t :-> TyVar w) s of
                         Left err -> addLog (show (t,t',w)) >> tyerr err
                         Right s' -> modify (first (const s')) >> lift (return $ findVar w s')
check (BinOp op e e') = do te <- checkAndUpdate e goDown
                           addLog $ "Operando izquierda (" ++ show e ++ "):" ++ show te 
                           te' <- checkAndUpdate e' goDownR
                           addLog $ "Operando derecha (" ++ show e' ++ "):" ++ show te'
                           tOp <- checkOp op
                           addLog $ "Operador " ++ show op ++" OK: " ++ show tOp
                           s <- getSub
                           w <- return $ newTyVar s (te :-> te' :-> tOp)
                           case unify (te :-> te' :-> TyVar w) tOp s of
                             Left err -> addLog (show w) >> tyerr err
                             Right s'  -> modify (first (const s')) >> 
                                         addLog ("Sustitución op-bin: " ++ show s') >>
                                         (lift . return) (findVar w s')
check (App e e') = do te <- checkAndUpdate e goDown
                      addLog "Funcion OK"
                      te' <- checkAndUpdate e' goDownR
                      addLog "Argumento OK"
                      s <- getSub
                      w <- return $ newTyVar s (te :-> te')
                      case unify te (te' :-> TyVar w) s of 
                        Left err -> tyerr err
                        Right s' -> modify (first (const s')) >> (lift . return) (findVar w s')
check (Quant q v r t) = do tyQ <- checkQuant q
                           addLog "Cuantificador OK"
                           ctx <- getCtx 
                           (ctx',tysV) <- lift . return $ removeVar ctx v
                           modify (second (const ctx'))
                           tyV <- checkAndUpdate (Var v) Just
                           addLog "Variable OK"
                           tyR <- checkAndUpdate r goDown
                           addLog "Rango OK"
                           tyT <- checkAndUpdate t goDownR
                           addLog "Termino OK"
                           case tyQ of 
                             t1 :-> t2 -> case (tyV `leq` t1, t2 `leq` tyT, tyR == tyBool) of
                                           (False,_,_) -> tyerr $ ErrNotExpected t1 tyV
                                           (_,False,_) -> tyerr $ ErrNotExpected tyBool tyR
                                           (_,_,False) -> tyerr $ ErrNotExpected t2 tyT
                                           (True,True,True) -> modify (second (\ctx -> addVar ctx v tysV)) >>
                                                              return tyT
                             t1 -> tyerr $ ErrNotExpected (tyV :-> tyT) t1
check (If b t f) = do tb <- checkAndUpdate b goDown
                      s <- getSub
                      case unify tb (TyAtom ATyBool) s of
                        Left err -> tyerr err
                        Right s' -> modify (first (const s')) >>
                                   checkAndUpdate t goIfTrue >>= \tt ->
                                   checkAndUpdate f goIfFalse >>= \tf ->
                                   if tt == tf 
                                   then return tb
                                   else tyerr $ ErrNotExpected tt tf
                                     
check (Case e cs) = do texp <- checkAndUpdate e goDown
                       -- TODO: qué pasa si cs es vacío?
                       -- En lo que sigue asumimos cs no vacío.
                       pats <- mapM checkCase cs
--                       pats <- return $ map fst pts
--                       ctx'' <- return . snd $ last pts
                       s <- getSub
                       let (Right subsPat) = unifyList (texp:map fst pats) s
                           subsExp = unifyList (map snd pats) subsPat
                       case (Right subsPat,subsExp) of
                         (Right s',Right s'') -> do
                                   modify (first (const s''))
                                   addLog $ "Sustitución Patterns: " ++ show s'
                                   addLog $ "Sustitución Cases: " ++ show s''
                                   updateCtxS <$> getSub
                                   return (rewrite s'' . fst $ head pats)
                         (Left err,_) -> tyerr err
                         (_,Left err) -> tyerr err


-- | Devuelve el tipo de un patrón y de la expresión.
checkCase :: (PreExpr,PreExpr) -> TyState ((Type,Type))
checkCase (pat,exp) = do s <- getSub
                         tpat <- check pat 
                         (updateCtxS <$> getSub)
--                         addLog $ "Contexto Patron ( " ++ show pat ++"): " ++ (show $ vars ctx2)
                         texp <- check exp
                         (updateCtxS <$> getSub)
--                         addLog $ "Contexto Expresión ( " ++ show exp ++"): " ++ (show $ vars ctx4)
                         modify (first (const s))
                         return (tpat,texp)
                          
initCtx :: Ctx
initCtx = Ctx { vars = M.empty
              , ops  = M.empty
              , cons = M.empty
              , quants = M.empty
              }

-- | Retorna el tipo de una expresi&#243;n bien tipada.
checkPreExpr :: PreExpr -> Either (TMErr,Log) Type
checkPreExpr e = case runRWS (runEitherT (check e)) (toFocus e) (emptySubst,initCtx) of
                   (res, _, l) -> either (\err -> Left (err,l)) Right res


typeCheckPreExpr :: PreExpr -> Either (TMErr,Log) PreExpr
typeCheckPreExpr e = case runRWS (runEitherT (check e)) (toFocus e) (emptySubst,initCtx) of
                   (res, (s,c), l) -> either (\err -> Left (err,l)) (const $ Right $ typing s c) res
    where
        typing :: TySubst -> Ctx -> PreExpr
        typing subst ctx = fmap (\v -> appSubst v $ M.lookup (varName v) (vars ctx)) e
            where appSubst v = maybe v (\t -> v {varTy = rewrite subst (last t) }) 

-- typeCheckPre :: PreExpr -> Either (TMErr,Log) PreExpr
typeCheckPre e = case runRWS (runEitherT (check e)) (toFocus e) (emptySubst,initCtx) of
                   (res, (s,_), l) -> l  -- either (\err -> Left (err,l)) (Right . typing s . fst) res
    where
        typing :: TySubst -> Ctx -> PreExpr
        typing subst ctx = fmap (\v -> appSubst v $ M.lookup (varName v) (vars ctx)) e
            where appSubst v = maybe v (\t -> v {varTy = rewrite subst (last t) }) 


getType :: PreExpr -> Maybe Type
getType = either (const Nothing) return . checkPreExpr