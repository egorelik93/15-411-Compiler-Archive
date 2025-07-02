module Compile.Types.X86_64 where

import Data.Char
import Data.Set (Set)
import qualified Data.Set as Set
import Text.PrettyPrint.HughesPJ

import Compile.Types.Assembly


data Instr a = MOVL a a
             | ADDL a a
             | SUBL a a
             | CLTD
             | IMULL a a
             | IDIVL a
             | NEGQ a
             | RET
             | SUBQ a a
             | ADDQ a a
             deriving (Eq, Show, Functor)

type Asm a = [Instr a]

data Register = EAX -- Return Register
              | EBX -- Must preserve
              | EDX -- Arg 4
              | ESI -- Arg 3
              | EDI -- Arg 2
              -- | EBP -- Must preserve
              -- | ESP -- Stack pointer
              | R8D -- Arg 5
              | R9D -- Arg 6
              | R10D -- Must save before calls
              | R12D -- Unused, must preserve
              | R13D -- Must preserve
              | R14D -- Must preserve
              | R15D -- Must preserve
                
              | R11D -- Linking, must save before calls
              | EBP -- Must preserve
              | RSP -- Stack pointer
              deriving (Eq, Show, Ord, Enum, Bounded)

data Loc = Reg Register
         | Deref Expr
         | DerefOffset Integer Expr
         deriving (Eq, Ord)

data Expr = Loc Loc
          | Const Integer
          deriving (Eq, Ord)

instance Show Loc where
  show (Reg r) = "%" ++ map toLower (show r)
  show (Deref l) = "(" ++ show l ++ ")"
  show (DerefOffset i l) = show i ++ show (Deref l)

instance Show Expr where
  show (Loc l) = show l
  show (Const i) = "$" ++ show i

instance Memory Expr where
  reg i | i <= fromEnum (maxBound :: Register) - 3 = Loc (Reg $ toEnum i)
        | otherwise = Loc $ DerefOffset offset (Loc (Reg RSP))
          where
            offset = fromIntegral $ 8 * (i - fromEnum (maxBound :: Register) + 3)
  constant i = Const $ fromIntegral i


spilled :: Instr Expr -> [Instr Expr]
spilled CLTD = [CLTD]
spilled RET = [RET]
spilled (NEGQ d) =
  case d of
    Loc (DerefOffset i e) -> [MOVL d (Loc $ Reg R11D),
                              NEGQ (Loc $ Reg R11D),
                              MOVL (Loc $ Reg R11D) d]
    _ -> [NEGQ d]
spilled (IDIVL s) =
  case s of
    Loc (DerefOffset i e) -> [MOVL s (Loc $ Reg R11D),
                              IDIVL (Loc $ Reg R11D)]
    _ -> [IDIVL s]
spilled i = restore ++ [fmap substitute i] ++ save
  where
    usedVars = Set.toList $ used i
    defVars = Set.toList $ defined i
    usedOffsetVars = [Loc (DerefOffset i e) | Loc (DerefOffset i e) <- usedVars]
    defOffsetVars = [Loc (DerefOffset i e) | Loc (DerefOffset i e) <- defVars]
    restore = do
      v <- usedOffsetVars
      if v `elem` defOffsetVars
        then [MOVL v (Loc $ Reg R11D)]
        else []
    save = do
      v <- defOffsetVars
      [MOVL (Loc $ Reg R11D) v]
    substitute x = if x `elem` defOffsetVars
                   then Loc $ Reg R11D
                   else x


instance (Memory m, Ord m) => Instruction (Instr m) m where
  used (MOVL s _) = Set.singleton s
  used (ADDL s d) = Set.fromList [s,d]
  used (SUBL s d) = Set.fromList [s,d]
  used CLTD = Set.singleton (reg 0)
  used (IMULL s d) = Set.fromList [s,d]
  used (IDIVL s) = Set.fromList [s, reg 0, reg 2]
  used (NEGQ s) = Set.singleton s
  used RET = Set.empty
  defined (MOVL _ d) = Set.singleton d
  defined (ADDL _ d) = Set.singleton d
  defined (SUBL _ d) = Set.singleton d
  defined CLTD = Set.fromList [reg 0, reg 2]
  defined (IMULL _ d) = Set.singleton d
  defined (IDIVL _) = Set.fromList [reg 0, reg 2]
  defined (NEGQ s) = Set.singleton s
  defined RET = Set.empty

interfere :: (Memory a, Eq a) => Instr a -> Set a -> Set a
interfere (MOVL s t) = Set.filter $ \v -> v /= t && v /= s
interfere (ADDL _ d) = Set.filter (/= d)
interfere (SUBL _ d) = Set.filter (/= d)
interfere CLTD = Set.filter $ \v -> v /= reg 0 && v /= reg 2
interfere (IMULL _ d) = Set.filter (/= d)
interfere (IDIVL _) = Set.filter $ \v -> v /= reg 0 && v /= reg 2
interfere (NEGQ d) = Set.filter (/= d)
interfere RET = \_ -> Set.empty

instr0 :: String -> Doc
instr0 = text

instr1 :: Show a => String -> a -> Doc
instr1 i a = text i <+> text (show a)

instr2 :: (Show a, Show b) => String -> a -> b -> Doc
instr2 i a b = text i <+> text (show a) <> comma <+> text (show b)

ppInstr :: Show a => Instr a -> Doc
ppInstr (MOVL s d) = instr2 "MOVL" s d
ppInstr (ADDL s d) = instr2 "ADDL" s d
ppInstr (SUBL s d) = instr2 "SUBL" s d
ppInstr CLTD = instr0 "CLTD"
ppInstr (IMULL s d) = instr2 "IMULL" s d
ppInstr (IDIVL d) = instr1 "IDIVL" d
ppInstr (NEGQ d) = instr1 "NEGL" d
ppInstr RET = instr0 "RET"
ppInstr (SUBQ s d) = instr2 "SUBQ" s d
ppInstr (ADDQ s d) = instr2 "ADDQ" s d

ppAsm :: Show a => Asm a -> Doc
ppAsm = foldr ($+$) empty . map ppInstr 

renderAsm :: Show a => Asm a -> String
renderAsm a = render $
              nest 4 (text ".globl _c0_main")
              $+$ text "_c0_main:"
              $+$ nest 4 code
              $+$ text ""
  where
    code = ppAsm a
