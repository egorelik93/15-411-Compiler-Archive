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
import Data.List (elemIndices, find, nub)

import Compile.Types


type Context = Map.Map Ident (C0Type Ident)

data SemanticError = DuplicateDeclaration Ident SourcePos
                   | TypeError String
                   | UndefinedVar (C0Type Ident) (Ident) String
                   | ErrorMsg String
                   deriving (Eq, Show)

instance Error SemanticError where
  strMsg = ErrorMsg

type TypeCheck a = ErrorT SemanticError (Reader (Map Ident (C0Type Ident))) a

type MaybeReturns = Env SourcePos (C0Type Ident, Bool)

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

assertExpType :: Monad m => C0Type Ident -> C0Type Ident
              -> SExpr (Value Ident)
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
subst ctx (TypeSynonym id) | take 7 id == "struct " = TypeSynonym id
{-  case Map.lookup id ctx of
    Nothing -> TypeSynonym id
    Just t -> subst ctx t-}
subst ctx (TypeSynonym id) = subst ctx (ctx ! id)
subst ctx (PointerType t) = PointerType $ subst ctx t
subst ctx (ArrayType t) = ArrayType $ subst ctx t
subst ctx (StructType id fs) = StructType id (map substDecl fs)
  where
    substDecl (VarDecl (PointerType t) i p) = VarDecl (PointerType t) i p
    substDecl (VarDecl (ArrayType t) i p) = VarDecl (ArrayType t) i p
    substDecl (VarDecl t i p) = VarDecl (subst ctx t) i p
subst cxt AnyType = AnyType

subst' :: Map Ident (C0Type Ident) -> C0Type Ident -> C0Type Ident
subst' ctx (TypeSynonym id) = subst' ctx (ctx ! id)
--subst' ctx (PointerType t) = PointerType $ subst' ctx t
--subst' ctx (ArrayType t) = ArrayType $ subst' ctx t
subst' ctx t = subst ctx t

hasVoid VoidType = True
hasVoid (PointerType t) = hasVoid t
hasVoid (ArrayType t) = hasVoid t
hasVoid (StructType _ fs) = any (\(VarDecl t _ _) -> hasVoid t) fs
hasVoid _ = False

checkAST = checkTopLevel Map.empty $
           Map.singleton "main" $ FnType [] IntType

checkTopLevel :: Map Ident (C0Type Ident)
              -> Context 
              -> AST Ident (SStmt Ident)
              -> Either SemanticError (Map Ident (C0Type Ident)
                                      , Context
                                      , Map Ident ([VarDecl Ident]
                                                  , TStmt Ident))
checkTopLevel ts ctx [] = Right (ts, ctx, Map.empty)
checkTopLevel ts ctx ((TypeDef t id pos) : rest) = let
  ts' = Map.insert id t ts
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
           case t of
             StructType s fs -> do
               let checkFields [] _ = return ()
                   checkFields (VarDecl t f pos : rest) fs =
                     if f `elem` fs
                     then throwError $ TypeError $
                          "Duplicate field name " ++ f ++ " in struct " ++ id
                          ++ " at " ++ show pos
                     else case subst' ts' t of
                       StructType i' _ | s == i' ->
                         throwError $ TypeError $
                         "cannot directly use struct as a " ++
                         "field type in another struct at "
                         ++ show pos
                       StructType _ fs' ->
                         checkFields fs' [] >> checkFields rest (f : fs)
                       _ -> checkFields rest (f : fs)
                in
                checkFields fs []
             _ -> return () 
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
      paramTypeCheck = do
        VarDecl t i pos <- params'
        return $
          assertMsgTE ("parameter " ++ i ++ " cannot be a struct at " ++ show pos)
           (case t of
               StructType _ _ -> False
               _ -> True
           )
  if nub (map fst paramNames) /= map fst paramNames
    then Left $ ErrorMsg $
          "Cannot have duplicate parameter names at "
          ++ show p
    else Right ()
  case paramNameCheck of
    [] -> return ()
    (x : _) -> x
  case paramTypeCheck of
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
      (subst ts out == IntType)
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
  (result, stmts') <- runReader (runErrorT $ checkStmt ctx'' stmts) ts
  case runEnv result of
    (pos, (t', will))
      | t' == out && (will || t' == VoidType) -> do
        (ts', ctx'', fns) <- checkTopLevel ts ctx' rest
        let fns' = Map.insertWithKey
                   (\k _ _ -> error $
                              "Disallowed repeated function definition of " ++ k ++ " at "
                              ++ show p)
                   id (params', stmts') fns
        return (ts', ctx'', fns')
      | t' == out -> Left $ ErrorMsg $ id ++ " not guaranteed to return"
      | otherwise -> Left $ TypeError $ "actual return type " ++ show (ppType t')
                     ++ " at " ++ show pos
                     ++" does not match declared return type "
                     ++ show (ppType out) ++ " for " ++ id
  

checkLValue :: Context -> SourcePos
            -> LValue Ident (SExpr (Value Ident))
            -> TypeCheck (SourcePos, C0Type Ident,
                          LValue Ident (TExpr (Value Ident)))
checkLValue ctx pos (Var v)  =
  case Map.lookup v ctx of
    Nothing -> throwError $ ErrorMsg $ 
               show v ++ " used without being declared at "
               ++ show pos
    Just t -> return (pos, t, Var v)
checkLValue ctx pos (Pointer v) = do
  (_, t, v') <- checkLValue ctx pos v
  ts <- lift ask
  case subst ts t of
    PointerType t' -> return (pos, subst ts t', Pointer v')
    _ -> throwError $ TypeError $
         "Attempt to assign by reference to a non-pointer at "
         ++ show pos ++ ": " ++ show (ppType t)
checkLValue ctx pos (Index v e) = do
  (_, e') <- checkExpr ctx e
  ts <- lift ask
  assertExpType IntType (subst ts $ typeOf e') e pos
  (_, t, v') <- checkLValue ctx pos v
  case subst ts t of
    ArrayType t' -> return (pos, subst ts t', Index v' e')
    _ -> throwError $ TypeError $
         "Attempt to assign to an index of a non-array at "
         ++ show pos
checkLValue ctx pos (Field v f) = do
  (_, t, v') <- checkLValue ctx pos v
  ts <- lift ask
  case subst' ts t of
    StructType s fs ->
      case find (\(VarDecl _ f' _) -> f' == f) fs of
        Just (VarDecl t' id _) ->
          return (pos, subst ts t', Field v' id)
        _ -> throwError $ TypeError $
             "struct " ++ s ++ " does not have a field named "
             ++ f ++ " at " ++ show pos
    _ -> throwError $ TypeError $
         "Attempt to obtain a field of a non-struct at " ++ show pos

checkStmt :: Context -> SStmt Ident
          -> TypeCheck (MaybeReturns, TStmt Ident)
checkStmt ctx (FMP.Pure e) = do
  let (pos, e') = runEnv e
  case e' of
    (FM.Pure e) | Effect <- snd (runEnv e) ->
      return (env pos (VoidType, True), return $ return $ env VoidType Effect)
    _ -> do
      (pos, t) <- checkExpr ctx e'
      case typeOf t of
        VoidType -> throwError $ TypeError $
                         "void function cannot be called in an expression at "
                         ++ show pos
        t' -> return (env pos $ (t', True), return t)
checkStmt ctx (FMP.Plus stmts) =
  case stmts of
    [] -> return (env (initialPos "Unknown") (VoidType, False), mzero)
    (s : ss) -> do
      (r1, s') <- checkStmt ctx s
      (r2, ss') <- checkStmt ctx (FMP.Plus ss)
      let (pos1, (t1, will1)) = runEnv r1
          (pos2, (t2, will2)) = runEnv r2
      if (t2 == VoidType) && not will2
        then return (env pos1 (t1, will1), s' <|> ss')
        else if (t1 == VoidType) && not will1
             then return (env pos2 (t2, will2), s' <|> ss')
             else do
               assertMsgT ("Conflicting return types " ++ show (ppType t1) ++
                           " at " ++ show pos1 ++
                           " and " ++ show (ppType t2) ++ " at " ++ show pos2)
                 (t1 == t2)
               return (env pos1 (t1, will1 || will2), s' <|> ss')
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
      (_, t) <- checkExpr ctx e
      return (env pos (VoidType, False), wrap $ Eval t)
    (pos, Assert e) -> do
      (pos', t) <- checkExpr ctx e
      ts <- lift ask
      assertExpType BoolType (subst ts $ typeOf t) e pos'
      return (env pos (VoidType, False), wrap $ Assert t)
    (pos, Declare (VarDecl AnyType id p) ss) -> do
      ts <- lift ask
      let getInitType (FMP.Plus (ss@(FMP.Plus _) : _)) =
            getInitType ss
          getInitType (FMP.Free s) =
            case snd $ runEnvT s of
              Declare _ ss -> getInitType ss
          getInitType ss@(FMP.Plus (FMP.Free s : ss')) =
            case snd $ runEnvT s of
              Assign (Var i) e | i == id -> do
                (_, t) <- checkExpr ctx e
                return $ typeOf t
              Declare _ ss -> getInitType ss
              _ -> getInitType (FMP.Plus ss')
          getInitType _ = throwError $ TypeError $
                          "Cannot infer the type of " ++ id
                          ++ " at " ++ show pos
      t <- getInitType ss
      checkStmt ctx $ wrap $ EnvT pos $ Declare (VarDecl t id p) ss
    (pos, Declare (VarDecl t' id p) ss) -> do
      ts <- lift ask
      let t = subst' ts t'
      case t of
        StructType _ _ -> throwError $ TypeError $
                          "variable " ++ id ++ " declared at " ++
                          show pos ++ " cannot have a struct type"
        _ -> return () 
      assertMsgT ("variable " ++ id ++ " declared at " ++ show pos
                  ++ " cannot be declared a type containing void")
        (not (hasVoid t))
      assertMsgT ("variable " ++ id ++ " cannot be a struct at " ++ show pos)
        (case t of
            StructType _ _ -> False
            _ -> True
        )
      case Map.lookup id ts of
        Just _ -> throwError $ ErrorMsg $ "Variable name " ++ id ++
                  " declared at " ++ show pos
                  ++ " cannot have the same name as type"
        Nothing -> return ()
      case Map.insertLookupWithKey (\ _ v _ -> v) id t ctx of
        (Just (FnType params out), ctx') -> do
          {-
          result <- case ss of
            FMP.Plus [FMP.Free (runEnvT -> (pos', Assign v e)), ss]
              | v == Var id -> do
                t' <- checkExpr ctx e
                assertMsgT
                  ("Declared type does not match assigned type at " ++ show pos)
                  (t == snd (runEnv t'))
                checkStmt ctx' ss
            _ -> checkStmt ctx' ss-}
          (result, ss') <- checkStmt ctx' ss
          if Set.member (pos, id) $
             live (Map.keysSet ctx')
             ss
            then throwError $ UndefinedVar t (id) $
                           show id ++ " used without being defined at "
                           ++ show pos
            else return (result, wrap $ Declare (VarDecl t id p) ss')
        (Just _, _) -> throwError $ ErrorMsg $ show id ++ " re-declared at " ++ show pos
        (Nothing, ctx') -> do
          (result, ss') <- checkStmt ctx' ss
          if Set.member (pos, id) $
             live (Map.keysSet ctx')
             ss
            then throwError $ UndefinedVar t (id) $
                           show id ++ " used without being defined at "
                           ++ show pos
            else return (result, wrap $ Declare (VarDecl t id p) ss')
    (pos, Assign v e) -> do
      (_, t, v') <- checkLValue ctx pos v
      (_, t') <- checkExpr ctx e
      ts <- lift ask
      assertMsgT
        ("Declared type " ++ show (ppType t) ++
         " does not match assigned type " ++
         show (ppType $ typeOf t') ++
         " at " ++ show pos)
        (subst ts t == subst ts (typeOf t'))
      return (env pos (VoidType, False), wrap $ Assign v' t')
    (pos, If cond thn els) -> do
      (_, t) <- checkExpr ctx cond
      assertExpType BoolType (typeOf t) cond pos
      (r1, thn') <- checkStmt ctx thn
      (r2, els') <- checkStmt ctx els
      let (pos1, (t1, will1)) = runEnv r1
          (pos2, (t2, will2)) = runEnv r2
      if not will1 && (t1 == VoidType)
        then return (env pos2 (t2, False), wrap $ If t thn' els')
        else if not will2 && (t2 == VoidType)
             then return (env pos1 (t1, False), wrap $ If t thn' els')
             else do
               assertMsgT ("Conflicting return types " ++ show (ppType t1) ++
                           " at " ++ show pos1 ++
                           " and " ++ show (ppType t2) ++ " at " ++ show pos2)
                 (t1 == t2)
               return (env pos1 (t1, will1 && will2), wrap $ If t thn' els')
    (pos, While cond blk) -> do
      (_, t) <- checkExpr ctx cond
      assertExpType BoolType (typeOf t) cond pos
      (t', blk') <- checkStmt ctx blk
      let (pos, (t'', _)) = runEnv t'
      return (env pos (t'', False), wrap $ While t blk')

checkExpr :: Context -> SExpr (Value Ident)
          -> TypeCheck (SourcePos, TExpr (Value Ident))
checkExpr ctx (FM.Pure e) =
  case runEnv e of
    (pos, Int i) -> return (pos, return $ env IntType (Int i))
    (pos, Bool b) -> return (pos, return $ env BoolType (Bool b))
    (pos, VarVal v) ->
      case Map.lookup v ctx of
        Nothing -> throwError $ ErrorMsg $ 
                   show v ++ " used without being declared at "
                   ++ show pos
        {-
        Just (t, False) -> throwError $ UndefinedVar t (LVal (Var v)) $
                           show v ++ " used without being defined at "
                           ++ show pos
-}
        Just t -> return (pos, return $ env t $ VarVal v)
    (pos, NULL) -> return (pos, return $ env (PointerType AnyType) $ NULL)
checkExpr ctx (FM.Free e) =
  case runEnvT e of
    (pos, Cond e1 e2 e3) -> do
      (_, t1) <- checkExpr ctx e1
      assertExpType BoolType (typeOf t1) e1 pos
      (pos2, t2) <- checkExpr ctx e2
      (_, t3) <- checkExpr ctx e3
      assertMsgT ("void not allowed in expression at "
                  ++ show pos2)
        (typeOf t2 /= VoidType)
      assertExpType (typeOf t2) (typeOf t3) e3 pos
      case typeOf t3 of
        AnyType -> return (pos, wrap $ EnvT (typeOf t2) $ Cond t1 t2 t3)
        _ -> return (pos, wrap $ EnvT (typeOf t3) $ Cond t1 t2 t3)
    (pos, BinOp op e1 e2) | op `elem` [Lt, LtE, Gt, GtE] -> do
      (_, t1) <- checkExpr ctx e1
      assertExpType IntType (typeOf t1) e1 pos
      (_, t2) <- checkExpr ctx e2
      assertExpType IntType (typeOf t2) e2 pos
      return (pos, wrap $ EnvT BoolType $ BinOp op t1 t2)
    (pos, BinOp op e1 e2) | op `elem` [Eq, NEq] -> do
      (_, t1) <- checkExpr ctx e1
      (pos2, t2) <- checkExpr ctx e2
      ts <- lift ask
      case subst' ts (typeOf t1) of
        StructType _ _ -> throwError $ TypeError $
                          "Cannot compare struct values at "
                          ++ show pos
        _ -> return ()
      assertMsgT ("void not allowed in expression at "
                  ++ show pos2)
        (typeOf t2 /= VoidType)
      assertExpType (typeOf t1) (typeOf t2) e2 pos
      return (pos, wrap $ EnvT BoolType $ BinOp op t1 t2)
    (pos, BinOp op e1 e2) -> do
      (_, t1) <- checkExpr ctx e1
      assertExpType IntType (typeOf t1) e1 pos
      (_, t2) <- checkExpr ctx e2
      assertExpType IntType (typeOf t2) e2 pos
      return (pos, wrap $ EnvT IntType $ BinOp op t1 t2)
    (pos, UnOp Not e) -> do
      (_, t) <- checkExpr ctx e
      assertExpType BoolType (typeOf t) e pos
      return (pos, wrap $ EnvT (typeOf t) $ UnOp Not t)
    (pos, UnOp op e) -> do
      (_, t) <- checkExpr ctx e
      assertExpType IntType (typeOf t) e pos
      return (pos, wrap $ EnvT (typeOf t) $ UnOp op t)
    (pos, Call f es) -> do
      esTypes <- mapM (checkExpr ctx) es
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
          for matchTypes $ \(e, (pos, t),t') -> assertExpType (typeOf t) t' e pos
          return (pos, wrap $ EnvT out $ Call f $ map snd esTypes)
        _ -> throwError $ ErrorMsg $ "Cannot call shadowed function "
             ++ f ++ " at " ++ show pos
    (pos, Deref (FM.Pure (snd . runEnv -> NULL))) ->
       throwError $ TypeError $
             "Cannot dereference NULL at " ++ show pos
    (pos, Deref e) -> do
      (_, t) <- checkExpr ctx e
      ts <- lift ask
      case typeOf t of
        PointerType AnyType -> throwError $ TypeError $
             "Cannot dereference NULL at " ++ show pos
        PointerType t' -> return (pos, wrap $ EnvT (subst' ts t') $ Deref t)
        _ -> throwError $ TypeError $
             "Dereferenced expression at " ++ show pos ++ " is not a pointer"
    (pos, Alloc t) -> do
      ts <- lift ask
      let t' = subst' ts t
      assertMsgT ("Cannot allocate void type at " ++ show pos) (not (hasVoid t'))
      return (pos, wrap $ EnvT (PointerType t) $ Alloc (subst' ts t'))
    (pos, Elt a i) -> do
      (_, a') <- checkExpr ctx a
      ts <- lift ask
      case typeOf a' of
        ArrayType t' -> do
          (_, i') <- checkExpr ctx i
          assertExpType IntType (typeOf i') i pos
          return (pos, wrap $ EnvT (subst' ts t') $ Elt a' i')
        _ -> throwError $ TypeError $
             "Indexed expression at " ++ show pos ++ " is not an array"
    (pos, AllocArray t e) -> do
      ts <- lift ask
      let t' = subst' ts t
      assertMsgT ("Cannot allocate void type at " ++ show pos) (not (hasVoid t'))
      (_, e') <- checkExpr ctx e
      assertExpType IntType (typeOf e') e pos
      return (pos, wrap $ EnvT (ArrayType t) $ AllocArray (subst' ts t') e')
    (pos, Get e f) -> do
      (_, e') <- checkExpr ctx e
      ts <- lift ask
      case subst' ts $ typeOf e' of
        StructType s fs ->
          case find (\(VarDecl _ f' _) -> f' == f) fs of
            Just (VarDecl t' id _) ->
              return (pos, wrap $ EnvT (subst' ts t') $ Get e' id)
            _ -> throwError $ TypeError $
                 "struct " ++ s ++ " does not have a field named "
                 ++ f ++ " at " ++ show pos
        _ -> throwError $ TypeError $
             "Attempt to obtain a field of a non-struct at " ++ show pos
