module Compile.TypeChecker where

import Prelude hiding (mapM)
import Control.Monad.State hiding (mapM)
import Control.Monad.Error hiding (mapM)
import Control.Monad.Identity hiding (mapM)
import Control.Monad.Reader hiding (mapM)
import Control.Monad hiding (mapM)
import Text.Parsec.Pos (SourcePos, initialPos)
import Control.Monad.Free.Class
import qualified Control.Monad.Free as FM
import qualified Control.MonadOr.Free as FMP
import Control.Comonad.Trans.Env hiding (ask)
import Control.Applicative
import Data.Traversable (mapM, for)
import Data.Set (Set)
import qualified Data.Set as Set
import Debug.Trace

import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.List (elemIndices)

import Compile.Types


type Context = Map.Map Ident (C0Type Ident)

data SemanticError = DuplicateDeclaration Ident SourcePos
                   | TypeError String
                   | UndefinedVar (C0Type Ident) (Value Ident) String
                   | ErrorMsg String
                   deriving (Eq, Show)

instance Error SemanticError where
  strMsg = ErrorMsg

type TypeCheck a = ErrorT SemanticError (Reader (Map Ident (C0Type Ident))) a

type MaybeReturns = Env SourcePos (C0Type Ident, Bool)

both :: TypeCheck MaybeReturns -> TypeCheck MaybeReturns
    -> TypeCheck MaybeReturns
both e1 e2 = do
  r1 <- e1
  r2 <- e2
  let (pos1, (t1, will1)) = runEnv r1
      (pos2, (t2, will2)) = runEnv r2
  if not will1 && (t1 == VoidType)
    then return $ env pos2 (t2, False)
    else if not will2 && (t2 == VoidType)
         then return $ env pos1 (t1, False)
         else do
           assertMsgT ("Conflicting return types " ++ show (ppType t1) ++
                       " at " ++ show pos1 ++
                       " and " ++ show (ppType t2) ++ " at " ++ show pos2)
             (t1 == t2)
           return $ env pos1 (t1, will1 && will2)

eitherOr :: TypeCheck MaybeReturns -> TypeCheck MaybeReturns
    -> TypeCheck MaybeReturns
eitherOr e1 e2 = do
  r1 <- e1
  r2 <- e2
  let (pos1, (t1, will1)) = runEnv r1
      (pos2, (t2, will2)) = runEnv r2
  if (t2 == VoidType) && not will2
    then return $ env pos1 (t1, will1)
    else if (t1 == VoidType) && not will1
         then return $ env pos2 (t2, will2)
         else do
           assertMsgT ("Conflicting return types " ++ show (ppType t1) ++
                       " at " ++ show pos1 ++
                       " and " ++ show (ppType t2) ++ " at " ++ show pos2)
             (t1 == t2)
           return $ env pos1 (t1, will1 || will2)

assertMsg :: (Monad m) => String -> Bool -> ErrorT SemanticError m ()
assertMsg s True  = return ()
assertMsg s False = throwError (ErrorMsg s)

assertMsgT :: (Monad m) => String -> Bool -> ErrorT SemanticError m ()
assertMsgT s True  = return ()
assertMsgT s False = throwError (TypeError s)

assertMsgE :: String -> Bool -> Either SemanticError ()
assertMsgE s True  = Right ()
assertMsgE s False = Left (ErrorMsg s)

assertMsgTE :: String -> Bool -> Either SemanticError ()
assertMsgTE s True  = Right ()
assertMsgTE s False = Left (TypeError s)

assertExpType :: Monad m => C0Type Ident -> C0Type Ident -> SExpr Ident
              -> SourcePos -> ErrorT SemanticError m ()
assertExpType t1 t2 e pos =
  assertMsgT ("Couldn't match expected type "
             ++ show (ppType t1) ++ " with actual type "
             ++ show (ppType t2) ++ " in expression "
             ++ show (ppExpr e) ++ " at "
             ++ show pos)
             (t1 == t2)



subst :: Map Ident (C0Type Ident) -> C0Type Ident -> C0Type Ident
subst _ IntType = IntType
subst _ BoolType = BoolType
subst _ VoidType = VoidType
subst ctx (FnType params t) = FnType (map (subst ctx) params) (subst ctx t)
subst ctx (TypeSynonym id) = subst ctx (ctx ! id)

checkAST = checkTopLevel Map.empty $
           Map.singleton "main" $ FnType [] IntType

checkTopLevel :: Map Ident (C0Type Ident)
              -> Context 
              -> AST Ident (SStmt Ident)
              -> Either SemanticError (Map Ident (C0Type Ident), Context)
checkTopLevel ts ctx [] = Right (ts, ctx)
checkTopLevel ts ctx ((TypeDef t id pos) : rest) = let
  ts' = Map.insert id (subst ts t) ts
  in
   case Map.lookup id ctx of
     Just _ -> Left $ ErrorMsg $ "Type name " ++ id ++
               " defined at " ++ show pos
                  ++ " cannot have the same name as a function"
     Nothing ->
       case Map.lookup id ts of
         Just _ -> Left $ ErrorMsg $ "Repeated typedef of " ++ id
                   ++ " at " ++ show pos
         Nothing -> do
           assertMsgE ("Cannot typedef void at " ++ show pos)
             (t /= VoidType)
           checkTopLevel ts' ctx rest
checkTopLevel ts ctx ((FnDecl (VarDecl t id p) params) : rest) = do
    let substDecl (VarDecl t i p) = VarDecl (subst ts t) i p
        params' = map substDecl params
        out = subst ts t
        getType (VarDecl t _ _) = t
        getName (VarDecl _ i pos) = (i, pos)
        paramTypes = map getType params'
        paramNames = map getName params'
        paramNameCheck = do
          (i, pos) <- paramNames
          case Map.lookup i ts of
            Just _ -> return $
                      Left $ ErrorMsg $ "Variable name " ++ id ++
                      " declared at " ++ show pos
                      ++ " cannot have the same name as type"
            Nothing -> [] {-
              case assertMsgE
                   ("Parameter name " ++ i ++ " at " ++ show pos ++
                    " shadows function name")
                   (i /= id)
              of
                Left e -> return $ Left e
                Right () -> []-}
    case paramNameCheck of
      [] -> return ()
      (x : _) -> x
    assertMsgTE ("function " ++ id ++ " declared at " ++ show p
                ++ " cannot have any void arguments")
      (not (VoidType `elem` paramTypes))
    case Map.lookup id ts of
     Just _ -> Left $ ErrorMsg $ "function " ++ id ++
               " defined at " ++ show p
                  ++ " cannot have the same name as a type"
     Nothing -> return ()
    case Map.lookup id ctx of
      Nothing -> do
        let ctx' = Map.insert id (FnType paramTypes out) ctx
        checkTopLevel ts ctx' rest
      Just t -> do
        let names = [v | VarDecl _ v _ <- params']
            repeats = [n | n <- names, length (elemIndices n names) > 1]
        assertMsgE ("Repeated parameters " ++ show repeats ++ " at "
                    ++ show p) (length repeats == 0)
        assertMsgE ("Mismatched declaration types for "
                    ++ id ++ " at " ++ show p)
          (t == (FnType paramTypes out))
        checkTopLevel ts ctx rest
checkTopLevel ts ctx ((FnDef (VarDecl t id p) params stmts) : rest) = do
  let substDecl (VarDecl t i p) = VarDecl (subst ts t) i p
      params' = map substDecl params
      out = subst ts t
      getType (VarDecl t _ _) = t
      getName (VarDecl _ i pos) = (i, pos)
      paramTypes = map getType params'
      paramNames = map getName params'
      paramNameCheck = do
          (i, pos) <- paramNames
          case Map.lookup i ts of
            Just _ -> return $
                      Left $ ErrorMsg $ "Variable name " ++ id ++
                      " declared at " ++ show pos
                      ++ " cannot have the same name as type"
            Nothing -> []
              {-case assertMsgE
                   ("Parameter name " ++ i ++ " at " ++ show pos ++
                    " shadows function name")
                   (i /= id)
              of
                Left e -> return $ Left e
                Right () -> []-}
  case paramNameCheck of
    [] -> return ()
    (x : _) -> x
  assertMsgTE ("function " ++ id ++ " defined at " ++ show p
              ++ " cannot have any void arguments")
        (not (VoidType `elem` paramTypes))
  case Map.lookup id ts of
     Just _ -> Left $ ErrorMsg $ "function " ++ id ++
               " defined at " ++ show p
                  ++ " cannot have the same name as a type"
     Nothing -> return ()
  if id == "main"
    then do
    assertMsgE ("main cannot have any arguments") (length params == 0)
    assertMsgE ("main must be of type int")
      (out == IntType)
    else return ()
  ctx' <- case Map.lookup id ctx of
    Nothing -> return $ Map.insert id (FnType paramTypes out) ctx
    Just t -> do
      assertMsgE ("Mismatched declaration types for "
                  ++ id ++ " at " ++ show p)
        (t == (FnType paramTypes out))
      return ctx
  let paramCtx = Map.fromListWithKey
              (\k _ _ -> error $
                         "Repeated parameter " ++ k ++
                         " at " ++ show p)
              [(v, t) | VarDecl t v _ <- params']
      ctx'' = Map.union paramCtx ctx'
  result <- runReader (runErrorT $ checkStmt ctx'' stmts) ts
  case runEnv result of
    (pos, (t', will))
      | t' == out && (will || t' == VoidType) -> checkTopLevel ts ctx' rest
      | t' == out -> Left $ ErrorMsg $ id ++ " not guaranteed to return"
      | otherwise -> Left $ TypeError $ "actual return type " ++ show (ppType t')
                     ++ " at " ++ show pos
                     ++" does not match declared return type "
                     ++ show (ppType t) ++ " for " ++ id
  

checkStmt :: Context -> SStmt Ident
          -> TypeCheck MaybeReturns
checkStmt ctx (FMP.Pure e) = do
  let (pos, e') = runEnv e
  case e' of
    (FM.Pure e) | Effect <- snd (runEnv e) -> return $ env pos (VoidType, True)
    _ -> do
      t <- checkExpr ctx e'
      case runEnv t of
        (_, VoidType) -> throwError $ TypeError $
                         "void function cannot be called in an expression at "
                         ++ show pos
        (pos, t') -> return $ env pos $ (t', True)
checkStmt ctx (FMP.Plus stmts) =
  case stmts of
    [] -> return $ env (initialPos "Unknown") (VoidType, False)
    (s : ss) -> checkStmt ctx s `eitherOr` checkStmt ctx (FMP.Plus ss)
{-    `catchError` \e -> if will && not (any hasBlock ss)
                       then case e of
                         TypeError _ -> throwError e
                         _ -> return (Just (t, will), ctx', s')
                       else throwError e
        Nothing -> do
          (t, ctx'', ss') <- checkStmt ctx' $ FMP.Plus ss
          return (t, ctx'', s' <|> ss')
-}
checkStmt ctx (FMP.Free x) =
  case runEnvT x of
    (pos, Eval e) -> do
      checkExpr ctx e
      return $ env pos (VoidType, False)
    (pos, Assert e) -> do
      r <- checkExpr ctx e
      assertExpType BoolType (snd $ runEnv r) e (fst $ runEnv r)
      return $ env pos (VoidType, False)
    (pos, Declare (VarDecl t' id _) ss) -> do
      ts <- lift $ ask
      let t = subst ts t'
      assertMsgT ("variable " ++ id ++ " declared at " ++ show pos
                  ++ " cannot be declared void")
        (t /= VoidType)
      case Map.lookup id ts of
        Just _ -> throwError $ ErrorMsg $ "Variable name " ++ id ++
                  " declared at " ++ show pos
                  ++ " cannot have the same name as type"
        Nothing -> return ()
      case Map.insertLookupWithKey (\ _ v _ -> v) id t ctx of
        (Just (FnType params out), ctx') -> do
          result <- case ss of
            FMP.Plus [FMP.Free (runEnvT -> (pos', Assign v e)), ss]
              | v == Var id -> do
                t' <- checkExpr ctx e
                assertMsgT
                  ("Declared type does not match assigned type at " ++ show pos)
                  (t == snd (runEnv t'))
                checkStmt ctx' ss
            _ -> checkStmt ctx' ss
          if Set.member (pos, Var id) $
             live (Set.map Var $ Map.keysSet ctx')
             ss
            then throwError $ UndefinedVar t (LVal (Var id)) $
                           show id ++ " used without being defined at "
                           ++ show pos
            else return result
        (Just _, _) -> throwError $ ErrorMsg $ show id ++ " re-declared at " ++ show pos
        (Nothing, ctx') -> do
          result <- checkStmt ctx' ss
          if Set.member (pos, Var id) $
             live (Set.map Var $ Map.keysSet ctx')
             ss
            then throwError $ UndefinedVar t (LVal (Var id)) $
                           show id ++ " used without being defined at "
                           ++ show pos
            else return result
    (pos, Assign (Var id) e) ->
      case Map.lookup id ctx of
        Nothing -> throwError $ ErrorMsg $ 
                        show id ++ " not declared at " ++ show pos
        Just t -> do
          t' <- checkExpr ctx e
          assertMsgT
            ("Declared type does not match assigned type at " ++ show pos)
            (t == snd (runEnv t'))
          return $ env pos (VoidType, False)
    (pos, If cond thn els) -> do
      t <- checkExpr ctx cond
      assertExpType BoolType (snd $ runEnv t) cond pos
      checkStmt ctx thn `both` checkStmt ctx els
    (pos, While cond blk) -> do
      t <- checkExpr ctx cond
      assertExpType BoolType (snd $ runEnv t) cond pos
      t' <- checkStmt ctx blk
      let (pos, (t'', _)) = runEnv t'
      return $ env pos (t'', False)

checkExpr :: Context -> SExpr Ident -> TypeCheck (Env SourcePos (C0Type Ident))
checkExpr ctx (FM.Pure e) =
  case runEnv e of
    (pos, Int i) -> return $ env pos IntType
    (pos, Bool b) -> return $ env pos BoolType
    (pos, LVal (Var v)) ->
      case Map.lookup v ctx of
        Nothing -> throwError $ ErrorMsg $ 
                   show v ++ " used without being declared at "
                   ++ show pos
        {-
        Just (t, False) -> throwError $ UndefinedVar t (LVal (Var v)) $
                           show v ++ " used without being defined at "
                           ++ show pos
-}
        Just t -> return $ env pos t
checkExpr ctx (FM.Free e) =
  case runEnvT e of
    (pos, Cond e1 e2 e3) -> do
      t1 <- checkExpr ctx e1
      assertExpType BoolType (snd $ runEnv t1) e1 pos
      t2 <- checkExpr ctx e2
      t3 <- checkExpr ctx e3
      assertMsgT ("void not allowed in expression at "
                  ++ show (fst $ runEnv t2))
        (snd (runEnv t2) /= VoidType)
      assertExpType (snd $ runEnv t2) (snd $ runEnv t3) e3 pos
      return $ env pos (snd $ runEnv t3)
    (pos, BinOp op e1 e2) | op `elem` [Lt, LtE, Gt, GtE] -> do
      t1 <- checkExpr ctx e1
      assertExpType IntType (snd $ runEnv t1) e1 pos
      t2 <- checkExpr ctx e2
      assertExpType IntType (snd $ runEnv t2) e2 pos
      return $ env pos BoolType
    (pos, BinOp op e1 e2) | op `elem` [Eq, NEq] -> do
      t1 <- checkExpr ctx e1
      t2 <- checkExpr ctx e2
      assertMsgT ("void not allowed in expression at "
                  ++ show (fst $ runEnv t2))
        (snd (runEnv t2) /= VoidType)
      assertExpType (snd $ runEnv t1) (snd $ runEnv t2) e2 pos
      return $ env pos BoolType
    (pos, BinOp op e1 e2) -> do
      t1 <- checkExpr ctx e1
      assertExpType IntType (snd $ runEnv t1) e1 pos
      t2 <- checkExpr ctx e2
      assertExpType IntType (snd $ runEnv t2) e2 pos
      return $ env pos IntType
    (pos, UnOp Not e) -> do
      t <- checkExpr ctx e
      assertExpType BoolType (snd $ runEnv t) e pos
      return $ env pos (snd $ runEnv t)
    (pos, UnOp op e) -> do
      t <- checkExpr ctx e
      assertExpType IntType (snd $ runEnv t) e pos
      return $ env pos (snd $ runEnv t)
    (pos, Call f es) -> do
      esTypes' <- mapM (checkExpr ctx) es
      let esTypes = map runEnv esTypes'
      case Map.lookup f ctx of
        Nothing ->  throwError $ ErrorMsg $ 
                   show f ++ " called without being declared at "
                   ++ show pos
        Just (FnType params out) -> do
          assertMsgT (show f ++
                      " is called with the wrong number of arguments at "
                      ++ show pos)
            (length esTypes == length params)
          let matchTypes = zip3 es esTypes params
          for matchTypes $ \(e, (pos, t),t') -> assertExpType t t' e pos
          return $ env pos out
        _ -> throwError $ ErrorMsg $ "Cannot call shadowed function "
             ++ f ++ " at " ++ show pos
