module Compile.TypeChecker where

import Control.Monad.State
import Control.Monad.Error
import Control.Monad.Identity
import Control.Monad
import Text.Parsec.Pos (SourcePos)
import Control.Monad.Free.Class
import qualified Control.Monad.Free as FM
import qualified Control.MonadOr.Free as FMP
import Control.Comonad.Trans.Env
import Control.Applicative
import Debug.Trace

import qualified Data.Map as Map

import Compile.Types


type Context = Map.Map Ident (C0Type Ident, Bool)

data SemanticError = DuplicateDeclaration Ident SourcePos
                   | TypeError String
                   | UndefinedVar (C0Type Ident) (Value Ident) String
                   | ErrorMsg String
                   deriving (Eq, Show)

instance Error SemanticError where
  strMsg = ErrorMsg

type TypeCheck a = ErrorT SemanticError Identity a

type MaybeReturns = Maybe (C0Type Ident, Bool)

assertMsg :: (Monad m) => String -> Bool -> ErrorT SemanticError m ()
assertMsg s True  = return ()
assertMsg s False = throwError (ErrorMsg s)

assertMsgT :: (Monad m) => String -> Bool -> ErrorT SemanticError m ()
assertMsgT s True  = return ()
assertMsgT s False = throwError (TypeError s)

assertMsgE :: String -> Bool -> Either SemanticError ()
assertMsgE s True  = Right ()
assertMsgE s False = Left (ErrorMsg s)

assertExpType :: Monad m => C0Type Ident -> C0Type Ident -> SExpr Ident
              -> SourcePos -> ErrorT SemanticError m ()
assertExpType t1 t2 e pos =
  assertMsgT ("Couldn't match expected type "
             ++ show (ppType t1) ++ " with actual type "
             ++ show (ppType t2) ++ " in expression "
             ++ show (ppExpr e) ++ " at "
             ++ show pos)
             (t1 == t2)



checkAST :: AST Ident (SStmt Ident)
         -> Either SemanticError
            (AST Ident (Stmt Ident (Expr (Value Ident)) (Expr (Value Ident))))
checkAST [FnDef (VarDecl IntType "main" p) [] stmts] = do
  (returnType, _, stmts') <- runIdentity $ runErrorT $ checkStmt Map.empty stmts
  case returnType of
    Just (IntType, True) -> return $ [FnDef (VarDecl IntType "main" p) [] stmts']
    Just (t, True) -> Left $ TypeError $ "actual return type " ++ show (ppType t)
                      ++ " does not match declared return type "
                      ++ show (ppType IntType) ++ "that of main"
    _ -> Left $ ErrorMsg "main not guaranteed to return"
  

checkStmt :: Context -> SStmt Ident
          -> TypeCheck (MaybeReturns, Context,
                        Stmt Ident (Expr (Value Ident)) (Expr (Value Ident)))
checkStmt ctx (FMP.Pure e) = do
  (t, e) <- checkExpr ctx $ snd $ runEnv e
  return (Just (t, True), ctx, FMP.Pure e)
checkStmt ctx (FMP.Plus stmts) =
  case stmts of
    [] -> return (Nothing, ctx, FMP.Plus [])
    (s : ss) -> do
      (result, ctx', s') <- checkStmt ctx s
      case result of
        Just (t, will) -> do
          (t', ctx'', ss') <- checkStmt ctx' $ FMP.Plus ss
          case t' of
            Nothing -> return (Just (t, will), ctx'', s' <|> ss')
            Just (t', will') -> do
              assertMsgT ("Conflicting return types " ++ show (ppType t)
                         ++ " and " ++ show (ppType t'))
                (t == t')
              return (Just (t, will || will'), ctx'', s' <|> ss')
          `catchError` \e -> if will && not (any hasBlock ss)
                             then case e of
                               TypeError _ -> throwError e
                               _ -> return (Just (t, will), ctx', s')
                             else throwError e
        Nothing -> do
          (t, ctx'', ss') <- checkStmt ctx' $ FMP.Plus ss
          return (t, ctx'', s' <|> ss')
checkStmt ctx (FMP.Free x) =
  case runEnvT x of
    (pos, Eval e) -> do
      (t, e') <- checkExpr ctx e
      return (Nothing, ctx, wrap (Eval e'))
    (pos, Declare (VarDecl t id _) ss) ->
      case Map.insertLookupWithKey (\ _ v _ -> v) id (t, False) ctx of
        (Just _, _) -> throwError $ ErrorMsg $ show id ++ " re-declared at " ++ show pos
        (Nothing, ctx') -> do
          (t', ctx'', ss') <- checkStmt ctx' ss
          let combine k (t1, d1) (t2, d2) | k == id = (t1, d1)
                                          | otherwise = (t2, d2)
              ctx''' = Map.intersectionWithKey combine ctx ctx''
          return (t', ctx''', wrap $ Declare (VarDecl t id pos) ss')
    (pos, Assign (Var id) e) ->
      case Map.updateLookupWithKey (\ _ (t, _) -> Just (t, True)) id ctx of
        (Nothing, _) -> throwError $ ErrorMsg $ 
                        show id ++ " not declared at " ++ show pos
        (Just (t, _), ctx') -> do
          (t', e') <- checkExpr ctx e
          assertMsgT
            ("Declared type does not match assigned type at " ++ show pos)
            (t == t')
          return (Nothing, ctx', wrap $ Assign (Var id) e')
          `catchError`
            \err -> case err of
              UndefinedVar t' (LVal (Var id)) _ -> do
                let ctx'' = Map.update (\ (t, _) -> Just (t, True)) id ctx
                checkStmt ctx'' (FMP.Free x)
                throwError err
              _ -> throwError err
    (pos, If cond thn els) -> do
      (t, cond') <- checkExpr ctx cond
      assertExpType BoolType t cond pos
      (r1, ctx1, thn') <- checkStmt ctx thn
      (r2, ctx2, els') <- checkStmt ctx els
      let combine (t1, d1) (t2, d2) = (t1, d1 && d2)
          ctx' = Map.unionWith combine ctx1 ctx2
      case (r1, r2) of
        (Just (t1, w1), Just (t2, w2)) -> do
          assertMsgT ("if statement at " ++ show pos ++
                     " returns conflicting types " ++ show (ppType t1)
                     ++ " and " ++ show (ppType t2))
            (t1 == t2)
          return (Just (t1, w1 && w2), ctx', wrap $ If cond' thn' els')
        (Nothing, Just (t, _)) ->
          return (Just (t, False), ctx', wrap $ If cond' thn' els')
        (Just (t, _), Nothing) ->
          return (Just (t, False), ctx', wrap $ If cond' thn' els')
        (Nothing, Nothing) ->
          return (Nothing, ctx', wrap $ If cond' thn' els')
    (pos, While cond blk) -> do
      (t, cond') <- checkExpr ctx cond
      assertExpType BoolType t cond pos
      (r, _, blk') <- checkStmt ctx blk
      case r of
        Nothing -> return (Nothing, ctx, wrap $ While cond' blk')
        Just (t, _) -> return (Just (t, False), ctx, wrap $ While cond' blk')

checkExpr :: Context -> SExpr Ident -> TypeCheck (C0Type Ident, Expr (Value Ident))
checkExpr ctx (FM.Pure e) =
  case runEnv e of
    (pos, Int i) -> return (IntType, return $ Int i)
    (pos, Bool b) -> return (BoolType, return $ Bool b)
    (pos, LVal (Var v)) ->
      case Map.lookup v ctx of
        Nothing -> throwError $ ErrorMsg $ 
                   show v ++ " used without being declared at "
                   ++ show pos
        Just (t, False) -> throwError $ UndefinedVar t (LVal (Var v)) $
                           show v ++ " used without being defined at "
                           ++ show pos
        Just (t, True) -> return (t, return $ LVal (Var v))
checkExpr ctx (FM.Free e) =
  case runEnvT e of
    (pos, Cond e1 e2 e3) -> do
      (t1, e1') <- checkExpr ctx e1
      assertExpType BoolType t1 e1 pos
      (t2, e2') <- checkExpr ctx e2
      (t3, e3') <- checkExpr ctx e3
      assertExpType t2 t3 e3 pos
      return (t3, wrap $ Cond e1' e2' e3')
    (pos, BinOp op e1 e2) | op `elem` [Lt, LtE, Gt, GtE] -> do
      (t1, e1') <- checkExpr ctx e1
      assertExpType IntType t1 e1 pos
      (t2, e2') <- checkExpr ctx e2
      assertExpType IntType t2 e2 pos
      return (BoolType, wrap $ BinOp op e1' e2')
    (pos, BinOp op e1 e2) | op `elem` [Eq, NEq] -> do
      (t1, e1') <- checkExpr ctx e1
      (t2, e2') <- checkExpr ctx e2
      assertExpType t1 t2 e2 pos
      return (BoolType, wrap $ BinOp op e1' e2')
    (pos, BinOp op e1 e2) -> do
      (t1, e1') <- checkExpr ctx e1
      assertExpType IntType t1 e1 pos
      (t2, e2') <- checkExpr ctx e2
      assertExpType IntType t2 e2 pos
      return (IntType, wrap $ BinOp op e1' e2')
    (pos, UnOp Not e) -> do
      (t, e') <- checkExpr ctx e
      assertExpType BoolType t e pos
      return (t, wrap $ UnOp Not e')
    (pos, UnOp op e) -> do
      (t, e') <- checkExpr ctx e
      assertExpType IntType t e pos
      return (t, wrap $ UnOp op e')
