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
import qualified Control.MonadOr.Free as FMP
import Data.Monoid((<>), mempty)
import Control.Comonad.Trans.Env
import Debug.Trace

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
      if ss == [] && s == "main"
        then error $ "Empty function definition for " ++
             s ++ " at " ++ show pos
             ++ " is not allowed"
        else return ()
      ss' <- elaborateStmt ss
      return $ A.FnDef (A.VarDecl t' i pos) ps' ss'
    G.FDecl t s ps pos -> do
      ps' <- for ps $ elaborateParam
      t' <- elaborateType t
      i <- elaborateIdent s
      return $ A.FnDecl (A.VarDecl t' i pos) ps'
    G.TypeDef t id pos -> do
      t' <- elaborateType t
      id' <- elaborateIdent id
      return $ A.TypeDef t' id' pos
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
    G.BoolType -> return A.BoolType
    G.VoidType -> return A.VoidType
    G.DefType id -> return $ A.TypeSynonym id
    _ -> notYetImplemented t

elaborateStmt :: [G.Stmt] -> Elaboration (A.SStmt A.Ident)
elaborateStmt [] =  return mempty
elaborateStmt (s : ss) =
  case s of
    G.Multi (G.Block s') -> do
      scope <- elaborateStmt s'
      rest <- elaborateStmt ss
      return $ scope <> rest
    G.Simp (G.AsnLValue v a e pos) -> do
      val <- elaborateLValue v
      e' <- elaborateExp e
      ss' <- elaborateStmt ss
      asn <- elaborateAsn a val e' pos
      return $ asn <> ss'
    G.Simp (G.PostOp v op pos) -> do
      val <- elaborateLValue v
      ss' <- elaborateStmt ss
      let exp1 = return $ env pos $ A.Int 1
          var = return $ env pos $ A.LVal val
          add1 = case op of
            G.PP -> wrap $ EnvT pos $ A.BinOp Add var exp1
            G.MM -> wrap $ EnvT pos $ A.BinOp Sub var exp1
          assignment = wrap $ EnvT pos $ A.Assign val add1
      return $ assignment <> ss'
    G.Simp (G.Decl (G.Init t s e) pos) -> do
      e' <- elaborateExp e
      d <- elaborateVarDecl s t pos
      ss' <- elaborateStmt ss
      let var = A.Var s
          init = liftF $ EnvT pos $ A.Assign var e'
      return $ wrap $ EnvT pos $ A.Declare d $ FMP.Plus [init, ss']
    G.Simp (G.Decl (G.UnInit t s) pos) -> do
      d <- elaborateVarDecl s t pos
      ss' <- elaborateStmt ss
      return $ wrap $ EnvT pos $ A.Declare d $ FMP.Plus [ss']
    G.Simp (G.Exp e pos) -> do
      e' <- elaborateExp e
      ss' <- elaborateStmt ss
      return $ (wrap $ EnvT pos $ A.Eval e') <> ss'
    G.Control (G.Assert e pos) -> do
      e' <- elaborateExp e
      ss' <- elaborateStmt ss
      return $ (wrap $ EnvT pos $ A.Assert e') <> ss'
    G.Control (G.Return e pos) -> do
      e' <- case e of
        Just e -> elaborateExp e
        Nothing -> return $ return $ env pos A.Effect
      ss' <- elaborateStmt ss
      case ss' of
        FMP.Plus stmts -> return $ FMP.Plus (return (env pos e') : stmts)
        FMP.Pure _ -> return $ return $ env pos e'
        FMP.Free stmt -> return $ FMP.Plus [return (env pos e')] <> ss'
    G.Control (G.If exp stmt maybeElse pos) -> do
      e' <- elaborateExp exp
      thn <- elaborateStmt [stmt]
      els <- case maybeElse of
        Just stmt -> elaborateStmt [stmt]
        Nothing -> elaborateStmt []
      ss' <- elaborateStmt ss
      return $ wrap (EnvT pos $ A.If e' thn els) <> ss'
    G.Control (G.While exp stmt pos) -> do
      e' <- elaborateExp exp
      stmt' <- elaborateStmt [stmt]
      ss' <- elaborateStmt ss
      return $ wrap (EnvT pos $ A.While e' stmt') <> ss'
    G.Control (G.For (i, e, u) stmt pos) -> do
      let loop = G.While e (G.Multi $ G.Block $
                            case u of
                              Just (G.Decl _ pos') ->
                                error ("Declarations not allowed " ++
                                       "in step portion of for loop at "
                                       ++ show pos')
                              Just u' -> [stmt, G.Simp u']
                              Nothing -> [stmt]
                           ) pos
      loop' <- elaborateStmt $
               case i of
                 Just i' -> [G.Simp i', G.Control loop]
                 Nothing -> [G.Control loop]
      ss' <- elaborateStmt ss
      return $ loop' <> ss'
    _ -> notYetImplemented s
      
elaborateAsn :: G.AsnOp -> A.LValue A.Ident -> A.SExpr A.Ident -> SourcePos
             -> Elaboration (A.SStmt A.Ident)
elaborateAsn a v e pos =
  case a of
    G.Asn -> return $ wrap $ EnvT pos $ A.Assign v e
    G.PAsn -> elaborateAsn G.Asn v (apply Add) pos
    G.MAsn -> elaborateAsn G.Asn v (apply Sub) pos
    G.TAsn -> elaborateAsn G.Asn v (apply Mul) pos
    G.DAsn -> elaborateAsn G.Asn v (apply Div) pos
    G.ModAsn -> elaborateAsn G.Asn v (apply Mod) pos
    G.ANDAsn -> elaborateAsn G.Asn v (apply AND) pos
    G.XORAsn -> elaborateAsn G.Asn v (apply XOR) pos
    G.ORAsn -> elaborateAsn G.Asn v (apply OR) pos
    G.SLAsn -> elaborateSLAsn
    G.SRAsn -> elaborateSRAsn
  where
    apply op = wrap $ EnvT pos $ A.BinOp op (return $ env pos $ A.LVal v) e
    const0 = return $ env pos $ A.Int 0
    const32 = return $ env pos $ A.Int 32
    testGtE0 = wrap $ EnvT pos $ A.BinOp GtE e const0
    testLt32 = wrap $ EnvT pos $ A.BinOp Lt e const32
    div0 = wrap $ EnvT pos $ A.BinOp Div const32 const0
    elaborateSLAsn = do
      let var = return $ env pos $ A.LVal v
          expr =
            case fmap (snd . runEnv) e of
              FM.Pure (A.Int i) ->
                if 0 <= i && i < 32
                then wrap $ EnvT pos $ A.BinOp SL var e
                else div0
              _ -> wrap $ EnvT pos $ A.Cond testGtE0
                   (wrap $ EnvT pos $ A.Cond testLt32
                    (wrap $ EnvT pos $ A.BinOp SL var e)
                    div0
                   )
                   div0
      return $ wrap $ EnvT pos $ A.Assign v expr
    elaborateSRAsn = do
      let var = return $ env pos $ A.LVal v
          expr =
            case fmap (snd . runEnv) e of
              FM.Pure (A.Int i) ->
                if 0 <= i && i < 32
                then wrap $ EnvT pos $ A.BinOp SR var e
                else div0
              _ -> wrap $ EnvT pos $ A.Cond testGtE0
                   (wrap $ EnvT pos $ A.Cond testLt32
                    (wrap $ EnvT pos $ A.BinOp SR var e)
                    div0
                   )
                   div0
      return $ wrap $ EnvT pos $ A.Assign v expr
          
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
    G.C0True pos -> return $ return $ env pos $ A.Bool True
    G.C0False pos -> return $ return $ env pos $ A.Bool False
    G.Val s pos -> do
      val <- elaborateLValue (G.Var s)
      return $ return (env pos $ A.LVal val)
    G.UnOp u e' pos -> do
      exp <- elaborateExp e'
      unop <- elaborateUnOp u
      return $ wrap $ EnvT pos $ A.UnOp unop exp
    G.BinOp G.And e1 e2 pos -> do
      e1' <- elaborateExp e1
      e2' <- elaborateExp e2
      let false = return $ env pos $ A.Bool False
      return $ wrap $ EnvT pos $ A.Cond e1' e2' false
    G.BinOp G.Or e1 e2 pos -> do
      e1' <- elaborateExp e1
      e2' <- elaborateExp e2
      let true = return $ env pos $ A.Bool True
      return $ wrap $ EnvT pos $ A.Cond e1' true e2'
    G.BinOp G.SL e1 e2 pos -> do
      e1' <- elaborateExp e1
      e2' <- elaborateExp e2
      let const0 = return $ env pos $ A.Int 0
          const32 = return $ env pos $ A.Int 32
          testGtE0 = wrap $ EnvT pos $ A.BinOp GtE e2' const0
          testLt32 = wrap $ EnvT pos $ A.BinOp Lt e2' const32
          div0 = wrap $ EnvT pos $ A.BinOp Div const32 const0
      case fmap (snd . runEnv) e2' of
        FM.Pure (A.Int i) ->
          if 0 <= i && i < 32
          then return $ wrap $ EnvT pos $ A.BinOp SL e1' e2'
          else return div0
        _ -> return $ wrap $ EnvT pos $ A.Cond testGtE0
             (wrap $ EnvT pos $ A.Cond testLt32
              (wrap $ EnvT pos $ A.BinOp SL e1' e2')
              div0
             )
             div0
    G.BinOp G.SR e1 e2 pos -> do
      e1' <- elaborateExp e1
      e2' <- elaborateExp e2
      let const0 = return $ env pos $ A.Int 0
          const32 = return $ env pos $ A.Int 32
          testGtE0 = wrap $ EnvT pos $ A.BinOp GtE e2' const0
          testLt32 = wrap $ EnvT pos $ A.BinOp Lt e2' const32
          div0 = wrap $ EnvT pos $ A.BinOp Div const32 const0
      case fmap (snd . runEnv) e2' of
        FM.Pure (A.Int i) ->
          if 0 <= i && i < 32
          then return $ wrap $ EnvT pos $ A.BinOp SR e1' e2'
          else return div0
        _ -> return $ wrap $ EnvT pos $ A.Cond testGtE0
             (wrap $ EnvT pos $ A.Cond testLt32
              (wrap $ EnvT pos $ A.BinOp SR e1' e2')
              div0
             )
             div0
    G.BinOp b e1 e2 pos -> do
      e1' <- elaborateExp e1
      e2' <- elaborateExp e2
      b' <- elaborateBinOp b
      return $ wrap $ EnvT pos $ A.BinOp b' e1' e2'
    G.Cond c1 c2 c3 pos -> do
      c1' <- elaborateExp c1
      c2' <- elaborateExp c2
      c3' <- elaborateExp c3
      return $ wrap $ EnvT pos $ A.Cond c1' c2' c3'
    G.Apply f params pos -> do
      params' <- mapM elaborateExp params
      return $ wrap $ EnvT pos $ A.Call f params'
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
    G.Lt -> return Lt
    G.LtE -> return LtE
    G.Gt -> return Gt
    G.GtE -> return GtE
    G.Eq -> return Eq
    G.NEq -> return NEq
    G.AND -> return AND
    G.XOR -> return XOR
    G.OR -> return OR
    G.SL -> return SL
    G.SR -> return SR

elaborateUnOp :: G.UnOp -> Elaboration Op
elaborateUnOp o =
  case o of
    G.Neg -> return Neg
    G.Bang -> return Not
    G.Comp -> return Comp
    _ -> notYetImplemented o
