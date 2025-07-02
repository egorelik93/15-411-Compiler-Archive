{- L1 Compiler
   Author: *[Redacted]
   Modified by: [Redacted]

   Defines a flat abstract assembly.
-}
module Compile.Types.AbstractAssembly where

import qualified Data.Set as Set

import Compile.Types.Ops
import Compile.Types.Assembly

data AAsm = AAsm {aAssign :: [ALoc]
                 ,aOp     :: Op
                 ,aArgs   :: [AVal]
                 }
          | ACtrl COp AVal
          | AComment String deriving (Eq, Show)

data AVal = ALoc ALoc
          | AImm Int deriving (Eq, Show, Ord)

data ALoc = AReg Int
          | ATemp Int deriving (Eq, Show, Ord)


instance Memory AVal where
  reg i = ALoc $ AReg i
  constant i = AImm i

instance Instruction AAsm AVal where
  used (AAsm _ _ a) = Set.fromList a
  used (ACtrl Ret v) = Set.singleton v
  used (AComment _) = Set.empty
  defined (AAsm d _ _) = Set.fromList $ map ALoc d
  defined (ACtrl Ret _) = Set.empty
  defined (AComment _) = Set.empty
  
