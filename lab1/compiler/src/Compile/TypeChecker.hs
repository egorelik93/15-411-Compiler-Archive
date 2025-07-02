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

import qualified Data.Map as Map

import Compile.Types


type Context = Map.Map Ident (C0Type Ident, Bool)

-- data SemanticError = DuplicateDeclaration Ident SourcePos

type TypeCheck a = ErrorT String Identity a


assertMsg :: (Monad m) => String -> Bool -> ErrorT String m ()
assertMsg s True  = return ()
assertMsg s False = throwError s

assertMsgE :: String -> Bool -> Either String ()
assertMsgE s True  = Right ()
assertMsgE s False = Left s


checkAST :: AST Ident (SStmt Ident)
         -> Either String
            (AST Ident (Stmt Ident (Expr (Value Ident)) (Expr (Value Ident))))
checkAST [FnDef (VarDecl IntType "main" p) [] stmts] = do
  (returnType, stmts') <- runIdentity $ runErrorT $ checkStmt Map.empty stmts
  assertMsgE "return values do not match that of main"
    (returnType == Just IntType)
  return $ [FnDef (VarDecl IntType "main" p) [] stmts']

checkStmt :: Context -> SStmt Ident
          -> TypeCheck (Maybe (C0Type Ident),
                        Stmt Ident (Expr (Value Ident)) (Expr (Value Ident)))
checkStmt ctx (FMP.Pure e) = do
  (t, e) <- checkExpr ctx $ snd $ runEnv e
  return (Just t, FMP.Pure e)
checkStmt ctx (FMP.Plus stmts) =
  case stmts of
    [] -> return (Nothing, FMP.Plus [])
    (s : ss) -> do
      (result, s') <- checkStmt ctx s
      case result of
        Just t -> return $ (Just t, s')
        Nothing -> do
          (t, ss') <- checkStmt ctx $ FMP.Plus ss
          return $ (t, s' <|> ss')
checkStmt ctx (FMP.Free x) =
  case runEnvT x of
    (pos, Declare (VarDecl t id _) ss) ->
      case Map.insertLookupWithKey (\ _ v _ -> v) id (t, False) ctx of
        (Just _, _) -> throwError $ show id ++ " re-declared at " ++ show pos
        (Nothing, ctx') -> do
          (t', ss') <- checkStmt ctx' ss
          return (t', wrap $ Declare (VarDecl t id pos) ss')
    (pos, Assign (Var id) e) ->
      case Map.updateLookupWithKey (\ _ (t, _) -> Just (t, True)) id ctx of
        (Nothing, _) -> throwError $
                        show id ++ " not declared at " ++ show pos
        (Just (t, _), ctx') -> do
          (t', e') <- checkExpr ctx e
          assertMsg
            ("Declared type does not match assigned type at " ++ show pos)
            (t == t')
          return (Nothing, wrap $ Assign (Var id) e')

checkExpr :: Context -> SExpr Ident -> TypeCheck (C0Type Ident, Expr (Value Ident))
checkExpr _ (FM.Pure e) = return (IntType, return $ snd $ runEnv e)
checkExpr ctx (FM.Free e) =
  case snd $ runEnvT e of
    BinOp op e1 e2 -> do
      (t1, e1') <- checkExpr ctx e1
      (t2, e2') <- checkExpr ctx e2
      return (IntType, wrap $ BinOp op e1' e2')
    UnOp op e -> do
      (t, e') <- checkExpr ctx e
      return (t, wrap $ UnOp op e')  
