{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Compile.Elaboration where

import Prelude hiding (lookup)
import Control.Monad.Trans
import Control.Monad.Error
import Data.Traversable (for)
import Text.Parsec (SourcePos)
import Control.Monad.Identity
import Control.Monad.Free.Class
import qualified Control.Monad.Free as FM
import qualified Control.MonadPlus.Free as FMP
import Data.Monoid((<>))
import Control.Comonad.Trans.Env

import Compile.Types.Ops
import qualified Compile.Types.Grammar as G
import qualified Compile.Types.AST as A


data ElaborationError = NotYetImplemented String
                      | UndeclaredVariableUsed G.Ident
                      | IntegerOutOfRange G.IntConst SourcePos
                      | ElaborationError String
                      deriving (Eq, Show)

instance Error ElaborationError where
  strMsg = ElaborationError

type Elaboration a = ErrorT ElaborationError Identity a


notYetImplemented :: Show a => a -> Elaboration b
notYetImplemented a = throwError $ NotYetImplemented $ show a


elaborate :: G.Program
          -> Either ElaborationError (A.AST A.Ident (A.SStmt A.Ident))
elaborate p = runIdentity $ runErrorT $ elaborateProgram p


elaborateIdent :: G.Ident -> Elaboration A.Ident
elaborateIdent s = return s

elaborateProgram :: G.Program
                 -> Elaboration (A.AST A.Ident (A.SStmt A.Ident))
elaborateProgram ds = for ds elaborateGDecl

elaborateGDecl :: G.GDecl
               -> Elaboration (A.TopLevelDecl A.Ident (A.SStmt A.Ident))
elaborateGDecl d =
  case d of
    G.FDef t s ps (G.Block ss) pos -> do
      ps' <- for ps $ elaborateParam
      t' <- elaborateType t
      i <- elaborateIdent s
      ss' <- elaborateStmt ss
      return $ A.FnDef (A.VarDecl t' i pos) ps' ss'
    _ -> notYetImplemented d

elaborateParam :: G.Param -> Elaboration (A.VarDecl A.Ident)
elaborateParam (G.Param t s pos) = elaborateVarDecl s t pos

elaborateVarDecl :: G.Ident -> G.C0Type -> SourcePos
                 -> Elaboration (A.VarDecl A.Ident)
elaborateVarDecl s t pos = do
  i <- elaborateIdent s
  t' <- elaborateType t
  return $ A.VarDecl t' i pos

elaborateType :: G.C0Type -> Elaboration (A.C0Type A.Ident)
elaborateType t =
  case t of
    G.IntType -> return A.IntType
    _ -> notYetImplemented t

elaborateStmt :: [G.Stmt] -> Elaboration (A.SStmt A.Ident)
elaborateStmt (s : ss) =
  case s of
    G.Simp (G.AsnLValue v a e pos) -> do
      val <- elaborateLValue v
      e' <- elaborateExp e
      ss' <- elaborateStmt ss
      asn <- elaborateAsn a val e' pos
      return $ asn <> ss' 
    G.Simp (G.Decl (G.Init t s e) pos) -> do
      e' <- elaborateExp e
      d <- elaborateVarDecl s t pos
      ss' <- elaborateStmt ss
      let var = A.Var s
          init = liftF $ EnvT pos $ A.Assign var e'
      return $ wrap $ EnvT pos $ A.Declare d $ init <> ss'
    G.Simp (G.Decl (G.UnInit t s) pos) -> do
      d <- elaborateVarDecl s t pos
      ss' <- elaborateStmt ss
      return $ wrap $ EnvT pos $ A.Declare d ss'
    G.Control (G.Return e pos) -> do
      e' <- elaborateExp e
      return $ return $ env pos e'
    _ -> notYetImplemented s
      
elaborateAsn :: G.AsnOp -> A.LValue A.Ident -> A.SExpr A.Ident -> SourcePos
             -> Elaboration (A.SStmt A.Ident)
elaborateAsn a v e pos =
  case a of
    G.Asn -> return $ wrap $ EnvT pos $ A.Assign v e
    G.PAsn -> return $ wrap $ EnvT pos $ A.Assign v (apply Add)
    G.MAsn -> return $ wrap $ EnvT pos $ A.Assign v (apply Sub)
    G.TAsn -> return $ wrap $ EnvT pos $ A.Assign v (apply Mul)
    G.DAsn -> return $ wrap $ EnvT pos $ A.Assign v (apply Div)
    G.ModAsn -> return $ wrap $ EnvT pos $ A.Assign v (apply Mod)
    _ -> notYetImplemented a
  where
    apply op = wrap $ EnvT pos $ A.BinOp op (return $ env pos $ A.LVal v) e
          
elaborateLValue :: G.LValue -> Elaboration (A.LValue A.Ident)
elaborateLValue v =
  case v of
    G.Var s -> return $ A.Var s
    G.ParenLValue v -> elaborateLValue v
    _ -> notYetImplemented v

elaborateExp :: G.Exp -> Elaboration (A.SExpr A.Ident)
elaborateExp e = do
  case e of
    G.ParenExp e' _ -> elaborateExp e'
    G.Int i pos -> elaborateIntConst i pos
    G.Val s pos -> do
      val <- elaborateLValue (G.Var s)
      return $ return (env pos $ A.LVal val)
    G.UnOp u e' pos -> do
      exp <- elaborateExp e'
      unop <- elaborateUnOp u
      return $ wrap $ EnvT pos $ A.UnOp unop exp
    G.BinOp b e1 e2 pos -> do
      e1' <- elaborateExp e1
      e2' <- elaborateExp e2
      b' <- elaborateBinOp b
      return $ wrap $ EnvT pos $ A.BinOp b' e1' e2'
    _ -> notYetImplemented e

elaborateIntConst :: G.IntConst -> SourcePos -> Elaboration (A.SExpr A.Ident)
elaborateIntConst (G.Dec n) pos
  | 0 <= n && n <= 2^31 = return $ return $ env pos $ A.Int n
  | otherwise = throwError $ IntegerOutOfRange (G.Dec n) pos
elaborateIntConst (G.Hex n) pos
  | 0x0 <= n && n <= 0xffffffff = return $ return $ env pos $ A.Int n
  | otherwise = throwError $ IntegerOutOfRange (G.Hex n) pos

elaborateBinOp :: G.BinOp -> Elaboration Op
elaborateBinOp o =
  case o of
    G.Plus -> return Add
    G.Minus -> return Sub
    G.Times -> return Mul
    G.Divide -> return Div
    G.Mod -> return Mod
    _ -> notYetImplemented o

elaborateUnOp :: G.UnOp -> Elaboration Op
elaborateUnOp o =
  case o of
    G.Neg -> return Neg
    _ -> notYetImplemented o
