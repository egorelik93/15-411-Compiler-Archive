module Compile.Types.X86_64 where

import Data.Char
import Data.Set (Set)
import qualified Data.Set as Set
import Text.PrettyPrint.HughesPJ
import Data.List(elemIndex)
import Numeric
import Debug.Trace

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
             | CALL String [a]
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
              | R12D -- Unused, must preserve
              | R13D -- Must preserve
              | R14D -- Must preserve
              | R15D -- Must preserve

              | R10D -- Must save before calls
              | R11D -- Linking, must save before calls
              | EBP -- Must preserve
              | RSP -- Stack pointer
              | CL
              deriving (Eq, Show, Ord, Enum, Bounded)

data Loc = Reg Register
         | Deref Expr
         | DerefOffset Integer Expr
         | DerefIndex Integer Expr Expr Size
         deriving (Eq, Ord)

data Expr = Loc Size Loc
          | Const Integer

instance Eq Expr where
  (Const i) == (Const j) = i == j
  (Loc _ i) == (Loc _ j) = i == j
  _ == _ = False

instance Ord Expr where
  compare (Const i) (Const j) = compare i j
  compare (Loc _ i) (Loc _ j) = compare i j
  compare (Loc _ _) (Const _) = LT
  compare (Const _) (Loc _ _) = GT

instance Show Loc where
  show (Reg r) = "%" ++ map toLower (show r)
  show (Deref l) = "(" ++ show l ++ ")"
  show (DerefOffset i l) = show i ++ show (Deref l)
  show (DerefIndex o x i s) = show' o ++ "(" ++ show x64 ++ ","
                              ++ show i64 ++ "," ++ show (bytes s)
                              ++ ")"
    where
      show' 0 = ""
      show' i = show i
      x64 = case x of
        Loc _ l -> Loc Q l
        _ -> x
      i64 = case i of
        Loc _ l -> Loc Q l
        _ -> i

instance Show Expr where
  show (Loc Q (Reg register)) = "%" ++ r64
    where r64 = case register of
            EAX ->  "rax"
            EBX ->  "rbx"
            EDX ->  "rdx"
            ECX ->  "rcx"
            ESI ->  "rsi"
            EDI ->  "rdi"
            R8D ->  "r8"
            R9D ->  "r9"
            R10D -> "r10"
            R12D -> "r12"
            R13D -> "r13"
            R14D -> "r14"
            R15D -> "r15"
            R11D -> "r11"
            EBP ->  "rbp"
            RSP -> "rsp"
  show (Loc _ l) = show l
  show (Const i) | i >= 0 = "$" ++ showInt i ""
                 | otherwise = "$" ++ showInt (2 ^ 32 + i) ""

instance Memory Expr where
  type MemoryLoc Expr = Loc
  constant i = Const $ fromIntegral i
  loc s l = Loc s l
  mem o x (Just i) s = loc s $ DerefIndex (fromIntegral o) x i s
  mem o x Nothing s = loc s $ DerefOffset (fromIntegral o) x
  onHeap = isMemory

instance Location Loc where
  reg i | i <= fromEnum (maxBound :: Register) - 5 = Reg $ toEnum i
        | otherwise = DerefOffset offset (Loc Q (Reg RSP))
          where
            offset = fromIntegral $ 8 * (i - fromEnum (maxBound :: Register) + 5)
  arg 0 = Reg EAX
  arg 1 = Reg EDI
  arg 2 = Reg ESI
  arg 3 = Reg EDX
  arg 4 = Reg ECX
  arg 5 = Reg R8D
  arg 6 = Reg R9D
  arg i = DerefOffset (fromIntegral $ 8 * (i - 7)) (Loc Q $ Reg RSP)

calleeSave :: Loc -> Bool
calleeSave (Reg EBX) = True
calleeSave (Reg EBP) = True
calleeSave (Reg R12D) = True
calleeSave (Reg R13D) = True
calleeSave (Reg R14D) = True
calleeSave (Reg R15D) = True
calleeSave (Reg RSP) = True
calleeSave _ = False


isMemory :: Expr -> Bool
isMemory (Loc _ (Reg _)) = False
isMemory (Loc _ _) = True
isMemory _ = False

spilled :: Instr Expr -> [Instr Expr]
spilled CLTD = [CLTD]
spilled RET = [RET]
spilled (CMPL a b) =
  case a of
    Loc s _ | isMemory a -> [MOVL a (Loc s $ Reg R11D),
                             CMPL (Loc s $ Reg R11D) b,
                             MOVL (Loc s $ Reg R11D) a]
    _ -> [CMPL a b]
spilled (NEGQ d) =
  case d of
    Loc s _ | isMemory d -> [MOVL d (Loc s $ Reg R11D),
                             NEGQ (Loc s $ Reg R11D),
                             MOVL (Loc s $ Reg R11D) d]
    _ -> [NEGQ d]
spilled (IDIVL s) =
  case s of
    Loc size _ | isMemory s -> [MOVL s (Loc size $ Reg R11D),
                                IDIVL (Loc size $ Reg R11D)]
    _ -> [IDIVL s]
spilled (CALL f p) = [CALL f p]
spilled i = if length usedOffsetVars + length defOffsetVars
               < Set.size (Set.union usedVars defVars)
            then [i]
            else restore ++ [fmap substitute i] ++ save
  where
    usedVars = case i of
      MOVL s _ -> Set.singleton s
      _ -> used i
    defVars = defined i
    usedOffsetVars = Set.toList $ Set.filter isMemory usedVars
    defOffsetVars = Set.toList $ Set.filter isMemory defVars
    sizeOf (Loc s _) = s
    sizeOf (Const _) = L
    restore = do
      v <- usedOffsetVars
      if v `elem` defOffsetVars
        then [MOVL v (Loc (sizeOf v) $ Reg R11D)]
        else []
    save = do
      v <- defOffsetVars
      [MOVL (Loc (sizeOf v) $ Reg R11D) v]
    substitute x = if x `elem` defOffsetVars
                   then Loc (sizeOf x) $ Reg R11D
                   else x


instance (Memory m, Ord m) => Instruction (Instr m) where
  type Val (Instr m) = m
  type Label (Instr m) = LineID String
  used (MOVL s d) | onHeap d = Set.fromList [s,d]
                  | otherwise = Set.singleton s
  used (ADDL s d) = Set.fromList [s,d]
  used (SUBL s d) = Set.fromList [s,d]
  used CLTD = Set.singleton (loc Q $ reg 0)
  used (IMULL s d) = Set.fromList [s,d]
  used (IDIVL s) = Set.fromList [s, loc Q $ reg 0, loc Q $ reg 2]
  used (NEGQ s) = Set.singleton s
  used RET = Set.singleton (loc Q $ reg 0)
  used (NOTL s) = Set.singleton s
  used (XORL s d) = Set.fromList [s,d]
  used (ORL s d) = Set.fromList [s,d]
  used (ANDL s d) = Set.fromList [s,d]
  used (SALL k s) = Set.fromList [k,s, loc Q $ reg 3]
  used (SARL k s) = Set.fromList [k,s, loc Q $ reg 3]
  used (TESTL a b) = Set.fromList [a,b]
  used (CMPL a b) = Set.fromList [a,b]
  used (CMOVE s d) = Set.fromList [s,d]
  used (CMOVNE s d) = Set.fromList [s,d]
  used (CMOVG s d) = Set.fromList [s,d]
  used (CMOVGE s d) = Set.fromList [s,d]
  used (CMOVL s d) = Set.fromList [s,d]
  used (CMOVLE s d) = Set.fromList [s,d]
  used (CALL _ v) = Set.fromList [loc Q $ arg i | i <- [1 .. length v]]
  used _ = Set.empty
  defined (MOVL _ d) = Set.singleton d
  defined (ADDL _ d) = Set.singleton d
  defined (SUBL _ d) = Set.singleton d
  defined CLTD = Set.fromList [loc Q $ reg 0, loc Q $ reg 2]
  defined (IMULL _ d) = Set.singleton d
  defined (IDIVL _) = Set.fromList [loc Q $ reg 0, loc Q $ reg 2]
  defined (NEGQ s) = Set.singleton s
  defined RET = Set.empty
  defined (NOTL s) = Set.singleton s
  defined (XORL _ d) = Set.singleton d
  defined (ORL _ d) = Set.singleton d
  defined (ANDL _ d) = Set.singleton d
  defined (SALL k s) = Set.fromList [s, loc Q $ reg 3]
  defined (SARL k s) = Set.fromList [s, loc Q $ reg 3]
  defined (CMOVE _ d) = Set.singleton d
  defined (CMOVNE _ d) = Set.singleton d
  defined (CMOVG _ d) = Set.singleton d
  defined (CMOVGE _ d) = Set.singleton d
  defined (CMOVL _ d) = Set.singleton d
  defined (CMOVLE _ d) = Set.singleton d
  defined (CALL _ _) = Set.fromList $ [loc Q $ reg x | x <- [2 .. 7]]
                       ++ [loc Q $ reg 0, loc Q $ reg 12, loc Q $ reg 13]
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
  -- label = Label

interfere :: (Memory a, Eq a, Ord a) => Instr a -> Set a -> Set a
interfere (MOVL s t) = Set.filter $ \v -> v /= t && v /= s
{-
interfere (ADDL _ d) = Set.filter (/= d)
interfere (SUBL _ d) = Set.filter (/= d)
interfere CLTD = Set.filter $ \v -> v /= reg 0 && v /= reg 2
interfere (IMULL _ d) = Set.filter (/= d)
interfere (IDIVL _) = Set.filter $ \v -> v /= reg 0 && v /= reg 2
interfere (NEGQ d) = Set.filter (/= d)
interfere RET = \_ -> Set.empty-}
interfere i = Set.filter (\e -> Set.notMember e $ defined i)

instr0 :: String -> Doc
instr0 = text

instr1 :: Show a => String -> a -> Doc
instr1 i a = text i <+> text (show a)

instr2 :: (Show a, Show b) => String -> a -> b -> Doc
instr2 i a b = text i <+> text (show a) <> comma <+> text (show b)

expr32To64 :: Expr -> Expr
expr32To64 (Loc _ locc) = Loc Q locc
expr32To64 c = c

expr64To32 :: Expr -> Expr
expr64To32 (Loc _ locc) = Loc L locc
expr64To32 c = c

ppInstr :: Instr Expr -> Doc
ppInstr (MOVL s d) =
  case (s, d) of
    (Loc L _, Loc Q _)
      | onHeap d -> instr2 "MOVSLQ" s (expr32To64 s)
                    $+$ instr2 "MOVQ" (expr32To64 s) d
      | otherwise -> instr2 "MOVSLQ" s d
    (Const _, Loc L _) -> instr2 "MOVL" s d
    (Loc L _, Loc L _) -> instr2 "MOVL" s d
    (Loc Q _, Loc L _) -> instr2 "MOVL" (expr64To32 s) d
    (Const _, Loc Q (Deref (Loc _ (Reg R10D)))) ->
      instr2 "MOVQ" s (Loc Q (Reg R11D))
      $+$ instr2 "MOVQ" (Loc Q (Reg R11D)) d
    (Const _, Loc Q (DerefOffset _ (Loc _ (Reg R10D)))) ->
      instr2 "MOVQ" s (Loc Q (Reg R11D))
      $+$ instr2 "MOVQ" (Loc Q (Reg R11D)) d
    (Const _, Loc Q _) | onHeap d -> instr2 "MOVQ" s (Loc Q (Reg R10D))
                                     $+$ instr2 "MOVQ" (Loc Q (Reg R10D)) d
    (_, Loc Q _) -> instr2 "MOVQ" s d
ppInstr (ADDL s d) =
  case (s,d) of 
    (Loc L _, Loc Q _) ->
      if onHeap s
      then (instr2 "MOVSLQ" s (Loc Q (Reg R10D)))
           $+$ (instr2 "ADDQ" (Loc Q (Reg R10D)) d)
      else (instr2 "MOVSLQ" s (expr32To64 s))
           $+$ (instr2 "ADDQ" (expr32To64 s) d)
    (Const _, Loc L _) -> instr2 "ADDL" s d
    (Loc L _, Loc L _) -> instr2 "ADDL" s d
    (Loc Q _, Loc L _) -> instr2 "ADDL" (expr64To32 s) d
    (_, Loc Q _) -> instr2 "ADDQ" s d
ppInstr (SUBL s d) =
  case (s,d) of 
    (Loc L _, Loc Q _) ->
      if onHeap s
      then (instr2 "MOVSLQ" s (Loc Q (Reg R10D)))
           $+$ (instr2 "SUBQ" (Loc Q (Reg R10D)) d)
      else (instr2 "MOVSLQ" s (expr32To64 s))
           $+$ (instr2 "SUBQ" (expr32To64 s) d)
    (Const _, Loc L _) -> instr2 "SUBL" s d
    (Loc L _, Loc L _) -> instr2 "SUBL" s d
    (Loc Q _, Loc L _) -> instr2 "SUBL" (expr64To32 s) d
    (_, Loc Q _) -> instr2 "SUBQ" s d
ppInstr CLTD = instr0 "CLTD"
ppInstr (IMULL s d) =
    case (s,d) of 
    (Loc L _, Loc Q _) ->
      if onHeap s
      then (instr2 "MOVSLQ" s (Loc Q (Reg R10D)))
           $+$ (instr2 "IMULQ" (Loc Q (Reg R10D)) d)
      else (instr2 "MOVSLQ" s (expr32To64 s))
           $+$ (instr2 "IMULQ" (expr32To64 s) d)
    (Const _, Loc L _) -> instr2 "IMULL" s d
    (Loc L _, Loc L _) -> instr2 "IMULL" s d
    (Loc Q _, Loc L _) -> instr2 "IMULL" (expr64To32 s) d
    (_, Loc Q _) -> instr2 "IMULQ" s d
ppInstr (IDIVL (Const i)) = (instr2 "MOVL" (Const i) (Loc L (Reg R10D)))
                            $+$ (instr1 "IDIVL" (Loc L (Reg R10D)))
ppInstr (IDIVL d) = instr1 "IDIVL" (expr64To32 d)
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
ppInstr (TESTL a b) =
    case (a,b) of 
    (Loc L _, Loc Q _) ->
      if onHeap a
      then (instr2 "MOVSLQ" a (Loc Q (Reg R10D)))
           $+$ (instr2 "TESTQ" (Loc Q (Reg R10D)) b)
      else (instr2 "MOVSLQ" a (expr32To64 a))
           $+$ (instr2 "TESTQ" (expr32To64 a) b)
    (Loc Q _, Loc L _) ->
      if onHeap b
      then (instr2 "MOVSLQ" b (Loc Q (Reg R10D)))
           $+$ (instr2 "TESTQ" a (Loc Q (Reg R10D)))
      else (instr2 "MOVSLQ" b (expr32To64 b))
           $+$ (instr2 "TESTQ" a (expr32To64 b))
    (Loc Q _, Loc Q _) -> instr2 "TESTQ" a b
    (Const _, Loc Q _) -> instr2 "TESTQ" a b
    (Loc Q _, Const _) -> instr2 "TESTQ" a b
    (_, _) -> instr2 "TESTL" a b
ppInstr (CMPL a b) = 
  case (a,b) of 
    (Loc L _, Loc Q _) ->
      if onHeap a
      then (instr2 "MOVSLQ" a (Loc Q (Reg R10D)))
           $+$ (instr2 "CMPQ" (Loc Q (Reg R10D)) b)
      else (instr2 "MOVSLQ" a (expr32To64 a))
           $+$ (instr2 "CMPQ" (expr32To64 a) b)
    (Loc Q _, Loc L _) ->
      if onHeap b
      then (instr2 "MOVSLQ" b (Loc Q (Reg R10D)))
           $+$ (instr2 "CMPQ" a (Loc Q (Reg R10D)))
      else (instr2 "MOVSLQ" b (expr32To64 b))
           $+$ (instr2 "CMPQ" a (expr32To64 b))
    (Loc Q _, Loc Q _) -> instr2 "CMPQ" a b
    (Const _, Loc Q _) -> instr2 "CMPQ" a b
    (Loc Q _, Const _) -> instr2 "CMPQ" a b
    (Loc Q _, Const _) -> instr2 "CMPQ" a b
    (Loc L _, Const _) -> (instr2 "MOVL" b (Loc L (Reg R10D)))
                          $+$ (instr2 "CMPL" a (Loc L (Reg R10D)))
    (Const a, Const b) -> (instr2 "MOVL" (Const $ a - b) (Loc L (Reg R10D)))
                          $+$ (instr2 "TESTL" (Loc L (Reg R10D)) (Loc L (Reg R10D)))
    (_, _) -> instr2 "CMPL" a b
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
ppInstr (CALL f _) = text "CALL" <+> text f

ppAsm :: Asm Expr -> Doc
ppAsm = foldr ($+$) empty . map ppInstr 

renderAsm :: Asm Expr -> String
renderAsm a = render $
              nest 4 code
              $+$ text ""
  where
    code = ppAsm a
