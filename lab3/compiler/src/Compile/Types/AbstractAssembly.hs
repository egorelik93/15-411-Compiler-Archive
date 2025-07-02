{- L1 Compiler
   Author: *[Redacted]
   Modified by: [Redacted]

   Defines a flat abstract assembly.
-}
module Compile.Types.AbstractAssembly where

import qualified Data.Set as Set
import Control.MonadOr.Free
import Control.Monad.Trans.Free (FreeF)
import qualified Control.Monad.Trans.Free as FMF
import Data.Functor.Constant

import Compile.Types.Ops
import Compile.Types.Assembly
-- import Compile.Types.AST

data AAsm = AAsm {aAssign :: [ALoc]
                 ,aOp     :: Op
                 ,aArgs   :: [AVal]
                 }
          | ACtrl COp AVal
          | AComment String
          | ALabel String
          | AGoto String
          | AIfGoto AVal Op AVal String
          | ACall String [AVal]
          deriving (Eq, Show)

data AVal = ALoc ALoc
          | AImm Int deriving (Eq, Show, Ord)

data ALoc = AReg Int
          | AArg Int
          | ATemp Int deriving (Eq, Show, Ord)


instance Memory AVal where
  reg i = ALoc $ AReg i
  constant i = AImm i
  arg i = ALoc $ AArg i

instance Instruction AAsm where
  type Val AAsm = AVal
  type Label AAsm = LineID String
  used (AAsm _ _ a) = Set.fromList a
  used (ACtrl Ret v) = Set.singleton v
  used (AComment _) = Set.empty
  defined (AAsm d _ _) = Set.fromList $ map ALoc d
  defined (ACtrl Ret _) = Set.empty
  defined (AComment _) = Set.empty
  successors (AAsm _ _ _) = Set.singleton NextLine
  successors (ACtrl Ret _) = Set.empty
  successors (AComment _) = Set.singleton NextLine
  successors (AGoto s) = Set.singleton (LineLabel s)
  successors (AIfGoto _ _ _ s) = Set.fromList [LineLabel s, NextLine]
  -- label = ALabel 


data AInstr id lbl exp = Define id exp
                       | IfElseGoto exp lbl lbl
                       | Goto lbl
                       deriving (Eq, Show, Functor)

data Labeled lbl blk = Labeled lbl blk blk
                       deriving (Eq, Show)

type Block id lbl exp = FreeF (Labeled lbl) (AInstr id (LineID lbl) exp)
type Asm id lbl exp ret = Free (Block id lbl exp) ret

{-
instance Instruction (AInstr ALoc lbl AVal) where
  type Val (AInstr ALoc String AVal) = AVal
  type Label (AInstr ALoc lbl AVal) = LineID lbl
  used (Define _ e) = Set.singleton e
  used (IfElseGoto e _) = Set.singleton e
  used (Goto _) = Set.empty
  defined (Define v _) = Set.singleton $ ALoc v
  defined _ = Set.empty
  successors (Define _ _) = Set.singleton NextLine
  successors (IfElseGoto _ thn els) = Set.fromList [lbl, els]
  successors (Goto lbl) = Set.singleton lbl

instance Instruction (Asm ALoc lbl (Expr AVal) AVal) where
  type Val (AInstr ALoc lbl (Expr AVal) AVal) = AVal
  type Label (AInstr ALoc lbl (Expr AVal) AVal) = LineID lbl
  used (Pure v) = Set.singleton v
  used (Plus ss) = Set.unions $ map used ss
  used (Free (FMF.Free (Labeled lbl blk end))) =
    Set.union (used blk) (used end)
  used (Free (FMF.Pure s)) =
    case s of
      Define _ e -> Set.singleton e
      IfElseGoto e _ _ -> Set.singleton e
      Goto _ -> Set.empty
  defined (Pure v) = Set.empty
  defined (Plus ss) = Set.unions $ map defined ss
  defined (Free (FMF.Free (Labeled lbl blk end))) =
    Set.union (defined blk) (defined end)
  defined (Free (FMF.Pure s)) =
    case s of
      Define d _ -> Set.singleton (ALoc d)
      IfElseGoto _ _ _ -> Set.empty
      Goto _ -> Set.empty
  successors (Pure v) = Set.empty
  successors (Plus []) = Set.singleton NextLine
  successors (Plus ss) = successors $ last ss
  successors (Free (FMF.Free (Labeled lbl blk end))) = successors end
  successors (Free (FMF.Pure s)) =
    case s of
      Define _ _ -> Set.singleton $ NextLine
      IfElseGoto _ thn els -> Set.fromList [thn, els]
      Goto lbl -> Set.singleton lbl
-}
