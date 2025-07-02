{- L1 Compiler
   Author: *[Redacted]
   Modified by: [Redacted]

   Beginnings of a typechecker
-}
module Compile.CheckAST where

import Control.Monad.State
import Control.Monad.Error
                                   
import Control.Monad

import qualified Data.Set as Set

import Compile.Types

-- Note to the student
-- When your checker gets larger, you may wish to formalize the state
-- a little more.

-- This is hacky and not designed to scale.

runErrorState :: ErrorT String (State s) a -> s -> Either String a
runErrorState m s = evalState (runErrorT m) s

assertMsg :: (Monad m) => String -> Bool -> ErrorT String m ()
assertMsg s True  = return ()
assertMsg s False = throwError s

assertMsgE :: String -> Bool -> Either String ()
assertMsgE s True  = Right ()
assertMsgE s False = Left s

chain :: Monad m => [m Bool] -> m Bool
chain [] = return False
chain (x : xs) = do
  b <- x
  if b then return True
    else chain xs

checkAST :: AST -> Either String ()
checkAST [FnDef (VarDecl IntType "main" _) [] stmts] = do
  let decls = [v | Declare v _ <- stmts]
  let variables = Set.fromList $ [ident | VarDecl _ ident _ <- decls]
  assertMsgE (findDuplicate decls)
             $ (length decls) == (Set.size variables)
  rets <- runErrorState (chain $ map checkStmt stmts)
          (Set.empty, Set.empty)
  assertMsgE "main does not return" rets

checkStmt :: Stmt -> ErrorT String (State (Set.Set Ident, Set.Set Ident)) Bool
checkStmt (Declare (VarDecl _ ident _) e) = do
  (vars, def) <- lift get
  if Set.member ident vars
    then throwError "Duplicate variable declaration"
    else return ()
  case e of
    Nothing -> put (Set.insert ident vars, def)
    Just e' -> do
      checkExpr e'
      lift $ put (Set.insert ident vars, Set.insert ident def)
  return False
checkStmt (Return e _) = do
  checkExpr e
  return True
checkStmt (Assign (Var i) m e p) = do
  (vars, defined) <- get
  assertMsg (i ++ " not declared at " ++ (show p)) (Set.member i vars)
  case m of
    Just _  -> assertMsg (i ++ " used undefined at " ++ (show p))
                         (Set.member i defined)
    Nothing -> return ()
  checkExpr e
  lift $ put (vars, Set.insert i defined)
  return False
checkStmt _ = return False

checkExpr (Int n p) =
  assertMsg ((show n) ++ " too large at " ++ (show p))
            (n < 2^32)
checkExpr (Val (Var s) p) = do
  (vars, defined) <- get
  assertMsg (s ++ " used undeclared at " ++ (show p)) (Set.member s vars)
  assertMsg (s ++ " used undefined at " ++ (show p)) (Set.member s defined)
checkExpr (BinOp _ e1 e2 _) = mapM_ checkExpr [e1, e2]
checkExpr (UnOp _ e _) = checkExpr e

findDuplicate xs = findDuplicate' xs Set.empty
  where findDuplicate' [] _ = error "no duplicate"
        findDuplicate' (VarDecl _ x pos : xs) s =
          if Set.member x s
            then x ++ " re-declared at " ++ (show pos)
            else findDuplicate' xs (Set.insert x s)
