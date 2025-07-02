{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Compile.Translation where

import Prelude hiding (mapM)
import Control.Monad.Trans.State
import Data.Map (Map, (!))
import Control.Monad.Trans
import qualified Data.Map as Map
import Control.Monad.Free.Class
import qualified Control.Monad.Free as FM
import qualified Control.MonadOr.Free as FMP
import Data.Traversable
import Text.Parsec.Pos (SourcePos)
import Data.Monoid

import Compile.Types

{-
type Alloc = (Map.Map String Int, Int)


translate :: Stmt Ident Expr -> Stmt AVal (Term AVal)-}


newtype Alloc a = Alloc (State Int a)
                deriving (Functor, Monad)

type Index = Map Ident ALoc

allocate :: Alloc a -> a
allocate (Alloc s) = evalState s 0

newIndex :: Alloc Int
newIndex = Alloc $ do
  n <- get
  put (n + 1)
  return n

newALoc :: Alloc ALoc
newALoc = do
  i <- newIndex
  return (ATemp i)

getALoc :: Monad a => Ident -> StateT Index a ALoc
getALoc id = do
  indexMap <- get
  return $ indexMap ! id


indexIdent :: Value Ident -> StateT Index Alloc AVal
indexIdent (Int i) = return $ AImm (fromIntegral i)
indexIdent (LVal (Var v)) = do
  indexMap <- get
  return $ ALoc $ indexMap ! v

indexExpr :: Expr (Value Ident)
          -> StateT Index Alloc (Expr AVal)
indexExpr = mapM indexIdent


indexStmt :: Stmt Ident (Expr (Value Ident)) (Expr (Value Ident))
          -> StateT Index Alloc (Stmt ALoc (Expr AVal) (Expr AVal))
indexStmt (FMP.Pure e) = fmap FMP.Pure $ indexExpr e
indexStmt (FMP.Plus s) = fmap FMP.Plus $ mapM indexStmt s
indexStmt (FMP.Free (Declare (VarDecl _ id _) block)) = do
  indexMap <- get
  aLoc <- lift newALoc
  put $ Map.insert id aLoc indexMap
  indexStmt block
indexStmt (FMP.Free (Assign (Var v) expr)) = do
  v' <- getALoc v
  expr' <- indexExpr expr
  return $ FMP.Free (Assign (Var v') expr')


translateStmt :: Stmt ALoc (Expr AVal) (Expr AVal)
              -> Alloc (Stmt ALoc (Term AVal) AVal)
translateStmt (FMP.Pure e) = translateExpr e
translateStmt (FMP.Plus s) = fmap FMP.Plus $ mapM translateStmt s
translateStmt (FMP.Free (Declare _ b)) = translateStmt b
translateStmt (FMP.Free (Assign v e)) = do
  s <- translateExpr e
  return $ do
    e' <- s
    v =: UnOp Nop e'
    

translateExpr :: Expr AVal
              -> Alloc (Stmt ALoc (Term AVal) AVal)
translateExpr (FM.Pure (AImm i)) = do
  store <- newALoc
  return $ do
    Var store =: UnOp Nop (AImm i)
    <> return (ALoc store)
translateExpr (FM.Pure (ALoc v)) = return $ FMP.Pure (ALoc v)
translateExpr (FM.Free (BinOp op e1 e2)) = do
  s1 <- translateExpr e1
  s2 <- translateExpr e2
  result <- newALoc
  return $ do
    v1 <- s1
    v2 <- s2
    Var result =: BinOp op v1 v2
    <> return (ALoc result)
translateExpr (FM.Free (UnOp op e)) = do
  s <- translateExpr e
  result <- newALoc
  return $ do
    v <- s
    Var result =: (UnOp op v)
    <> return (ALoc result)

translate :: AST Ident (Stmt Ident (Expr (Value Ident)) (Expr (Value Ident)))
          -> Alloc (Stmt ALoc (Term AVal) AVal)
translate [FnDef _ _ stmt] = evalStateT (indexStmt stmt) Map.empty
                             >>= translateStmt

codeGen :: Stmt ALoc (Term AVal) AVal -> Alloc [AAsm]
codeGen (FMP.Pure v) = return [ACtrl Ret v]
codeGen (FMP.Plus s) = fmap concat $ mapM codeGen s
codeGen (FMP.Free (Declare _ b)) = codeGen b
codeGen (FMP.Free (Assign (Var v) (BinOp op e1 e2))) =
  return [AAsm [v] op [e1, e2]]
codeGen (FMP.Free (Assign (Var v) (UnOp op e))) =
  return [AAsm [v] op [e]]
