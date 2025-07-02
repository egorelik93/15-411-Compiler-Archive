module Compile.Types.X86_64 where

import Data.Char
import Data.Set (Set)
import qualified Data.Set as Set
import Text.PrettyPrint.HughesPJ
import Data.List(elemIndex)
import Numeric

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
             | Label String
             | NOTL a
             | XORL a a
             | ORL a a
             | ANDL a a
             | SALL a a
             | SARL a a
             | CMPL a a
             | TESTL a a
             | JMP String
             | JE String
             | JNE String
             | JG String
             | JGE String
             | JL String
             | JLE String
             | CMOVE a a
             | CMOVNE a a
             | CMOVG a a
             | CMOVGE a a
             | CMOVL a a
             | CMOVLE a a
             deriving (Eq, Show, Functor)

type Asm a = [Instr a]

data Register = EAX -- Return Register
              | EBX -- Must preserve
              | EDX -- Arg 4
			  | ECX
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
              | CL
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
  show (Const i) = "$0x" ++ showHex i ""

instance Memory Expr where
  reg i | i <= fromEnum (maxBound :: Register) - 4 = Loc (Reg $ toEnum i)
        | otherwise = Loc $ DerefOffset offset (Loc (Reg RSP))
          where
            offset = fromIntegral $ 8 * (i - fromEnum (maxBound :: Register) + 4)
  constant i = Const $ fromIntegral i


spilled :: Instr Expr -> [Instr Expr]
spilled CLTD = [CLTD]
spilled RET = [RET]
spilled (CMPL a b) =
  case a of
    Loc (DerefOffset i e) -> [MOVL a (Loc $ Reg R11D),
                              CMPL (Loc $ Reg R11D) b,
                              MOVL (Loc $ Reg R11D) a]
    _ -> [CMPL a b]
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


instance (Memory m, Ord m) => Instruction (Instr m) where
  type Val (Instr m) = m
  used (MOVL s _) = Set.singleton s
  used (ADDL s d) = Set.fromList [s,d]
  used (SUBL s d) = Set.fromList [s,d]
  used CLTD = Set.singleton (reg 0)
  used (IMULL s d) = Set.fromList [s,d]
  used (IDIVL s) = Set.fromList [s, reg 0, reg 2]
  used (NEGQ s) = Set.singleton s
  used RET = Set.empty
  used (NOTL s) = Set.singleton s
  used (XORL s d) = Set.fromList [s,d]
  used (ORL s d) = Set.fromList [s,d]
  used (ANDL s d) = Set.fromList [s,d]
  used (SALL k s) = Set.fromList [k,s, reg 3]
  used (SARL k s) = Set.fromList [k,s, reg 3]
  used (TESTL a b) = Set.fromList [a,b]
  used (CMPL a b) = Set.fromList [a,b]
  used (CMOVE s d) = Set.fromList [s,d]
  used (CMOVNE s d) = Set.fromList [s,d]
  used (CMOVG s d) = Set.fromList [s,d]
  used (CMOVGE s d) = Set.fromList [s,d]
  used (CMOVL s d) = Set.fromList [s,d]
  used (CMOVLE s d) = Set.fromList [s,d]
  used _ = Set.empty
  defined (MOVL _ d) = Set.singleton d
  defined (ADDL _ d) = Set.singleton d
  defined (SUBL _ d) = Set.singleton d
  defined CLTD = Set.fromList [reg 0, reg 2]
  defined (IMULL _ d) = Set.singleton d
  defined (IDIVL _) = Set.fromList [reg 0, reg 2]
  defined (NEGQ s) = Set.singleton s
  defined RET = Set.empty
  defined (NOTL s) = Set.singleton s
  defined (XORL _ d) = Set.singleton d
  defined (ORL _ d) = Set.singleton d
  defined (ANDL _ d) = Set.singleton d
  defined (SALL k s) = Set.fromList [s, reg 3]
  defined (SARL k s) = Set.fromList [s, reg 3]
  defined (CMOVE _ d) = Set.singleton d
  defined (CMOVNE _ d) = Set.singleton d
  defined (CMOVG _ d) = Set.singleton d
  defined (CMOVGE _ d) = Set.singleton d
  defined (CMOVL _ d) = Set.singleton d
  defined (CMOVLE _ d) = Set.singleton d
  defined _ = Set.empty
  successors RET = Set.empty
  successors (JMP s) = Set.singleton (LineLabel s)
  successors (JE s) = Set.fromList [NextLine, LineLabel s]
  successors (JNE s) = Set.fromList [NextLine, LineLabel s]
  successors (JG s) = Set.fromList [NextLine, LineLabel s]
  successors (JGE s) = Set.fromList [NextLine, LineLabel s]
  successors (JL s) = Set.fromList [NextLine, LineLabel s]
  successors (JLE s) = Set.fromList [NextLine, LineLabel s]
  successors _ = Set.singleton NextLine
  label = Label

interfere :: (Memory a, Eq a, Ord a) => Instr a -> Set a -> Set a
interfere (MOVL s t) = Set.filter $ \v -> v /= t && v /= s
interfere (ADDL _ d) = Set.filter (/= d)
interfere (SUBL _ d) = Set.filter (/= d)
interfere CLTD = Set.filter $ \v -> v /= reg 0 && v /= reg 2
interfere (IMULL _ d) = Set.filter (/= d)
interfere (IDIVL _) = Set.filter $ \v -> v /= reg 0 && v /= reg 2
interfere (NEGQ d) = Set.filter (/= d)
interfere RET = \_ -> Set.empty
interfere i = Set.filter (\e -> Set.notMember e $ defined i)

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
ppInstr (NOTL s) = instr1 "NOTL" s
ppInstr (XORL s d) = instr2 "XORL" s d
ppInstr (ORL s d) = instr2 "ORL" s d
ppInstr (ANDL s d) = instr2 "ANDL" s d
ppInstr (SALL k s) = instr2 "SALL" k s
ppInstr (SARL k s) = instr2 "SARL" k s
ppInstr (TESTL a b) = instr2 "TESTL" a b
ppInstr (CMPL a b) = instr2 "CMPL" a b
ppInstr (JMP s) = text "JMP" <+> text s
ppInstr (JE s) = text "JE" <+> text s
ppInstr (JNE s) = text "JNE" <+> text s
ppInstr (JG s) = text "JG" <+> text s
ppInstr (JGE s) = text "JGE" <+> text s
ppInstr (JL s) = text "JL" <+> text s
ppInstr (JLE s) = text "JLE" <+> text s
ppInstr (Label s) = nest (-4) (text s <> char ':')
ppInstr (CMOVE s d) = instr2 "CMOVE" s d
ppInstr (CMOVNE s d) = instr2 "CMOVNE" s d
ppInstr (CMOVG s d) = instr2 "CMOVG" s d
ppInstr (CMOVGE s d) = instr2 "CMOVGE" s d
ppInstr (CMOVL s d) = instr2 "CMOVL" s d
ppInstr (CMOVLE s d) = instr2 "CMOVLE" s d

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
