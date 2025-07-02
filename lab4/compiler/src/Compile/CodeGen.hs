{- L1 Compiler
   Author: *[Redacted]
   Modified by: [Redacted]

   Currently just a pseudolanguage with 3-operand instructions and arbitrarily many temps.
-}
module Compile.CodeGen where

import Control.Monad.Trans.State

import Compile.Types
import qualified Data.Map as Map
import qualified Control.Monad.Free as FM
import qualified Control.MonadPlus.Free as FMP

type Alloc = (Map.Map String Int, Int)

codeGen :: AST -> [AAsm]
codeGen [FnDef _ _ stmts] = evalState program (Map.empty, 0)
  where
    program :: State Alloc [AAsm]
    program = fmap concat $ sequence $ map genStmt stmts
      

genStmt :: Stmt -> State Alloc [AAsm]
genStmt (Declare (VarDecl _ ident s) init) = do
  (a, n) <- get
  put (Map.insert ident n a, n + 1)
  case init of
    Nothing -> return []
    Just e -> genStmt $ Assign (Var ident) Nothing e s
genStmt (Return e _) = do
  (a, n) <- get
  return $ genExp (a, n + 1) e (ATemp n) ++ [ACtrl Ret $ ALoc $ ATemp n]
genStmt (Assign (Var v) o e s) = do
  (a, n) <- get
  let l = ATemp $ a Map.! v
      e' = case o of
        Nothing -> e
        Just op -> BinOp op (Val (Var v) s) e s
  return $ genExp (a, n) e' l

genExp :: Alloc -> Expr -> ALoc -> [AAsm]
genExp _ (Int n _) l = [AAsm [l] Nop [AImm $ fromIntegral n]]
genExp (a,_) (Val (Var s) _) l = [AAsm [l] Nop [ALoc $ ATemp $ a Map.! s]]
genExp (a,n) (BinOp op e1 e2 _) l = let
  i1 = genExp (a, n + 1) e1 (ATemp n)
  i2 = genExp (a, n + 2) e2 (ATemp $ n + 1)
  c  = [AAsm [l] op [ALoc $ ATemp n, ALoc $ ATemp $ n + 1]]
  in i1 ++ i2 ++ c
genExp (a,n) (UnOp op e _) l = let
  i1 = genExp (a, n + 1) e (ATemp n)
  c  = [AAsm [l] op [ALoc $ ATemp n]]
  in i1 ++ c

genTerm :: Alloc -> ALoc -> Term [AAsm] -> [AAsm]
genTerm (alloc, n) l t =
  case t of
    Int i _ -> [AAsm [l] Nop [AImm $ fromIntegral i]]
    BinOp op e1 e2 _ -> e1 ++ e2 ++ [
