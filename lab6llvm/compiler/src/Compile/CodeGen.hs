module Compile.CodeGen where

import Prelude hiding (mapM, sequence, msum, EQ)
import Control.Monad.Trans.State
import Data.Map (Map, (!))
import Control.Monad.Trans
import qualified Data.Map as Map
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad.Free.Class
import qualified Control.Monad.Free as FM
import qualified Control.MonadOr.Free as FMP
import qualified Control.Monad.Trans.Free as FMF
import Control.Comonad.Trans.Env
import Data.Traversable
import Data.Foldable (msum)
import Text.Parsec.Pos (SourcePos)
import Data.Monoid hiding ((<>))
import Data.Heap (MinHeap)
import qualified Data.Heap as Heap
import Data.List (find, reverse)
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Text.PrettyPrint.HughesPJ
-- import LLVM.General.AST (Named(..))
-- import qualified LLVM.General.AST as LLVM
-- import qualified LLVM.General.AST.Constant as LLVMC
-- import LLVM.General.AST.AddrSpace
-- import LLVM.General.AST.Name
-- import LLVM.General.AST.Global
-- import LLVM.General.AST.IntegerPredicate
-- import LLVM.General.AST.CallingConvention
import Debug.Trace

import Compile.Types
import Compile.Types.Assembly
import Compile.SymbolGen
import Compile.TypeChecker (subst, subst')
import Compile.Translation (true, false)
import Compile.Types.X86_64



ppDefine :: (Show val, Show asn) => Define asn (Term val) -> Doc
ppDefine (Define asn expr) =
  text (show asn) <+> text "<-" <+> ppTerm (fmap (parens . text . show) expr)

ppBlocks :: Show asn => Blocks asn (Term AVal) -> String
ppBlocks (_, blks) = show $ IntMap.foldWithKey
                     (\ i (defs, exit) doc ->
                        text (".l" ++ show i) $+$
                        nest 4 (vcat (map ppDefine defs) $+$
                                ppExit exit) $+$ doc)
                     (text "")
                     blks

ppSSA :: Show asn => SSA asn (Term AVal) -> String
ppSSA (_, blks) = show $ IntMap.foldWithKey
                  (\ i (live, defs, exit) doc ->
                    text (".l" ++ show i) <>
                    parens (hsep $ punctuate comma $ map (text . show) live)
                    $+$
                    nest 4 (vcat (map ppDefine defs) $+$
                            ppExit exit) $+$ doc)
                  (text "")
                  blks

ppSSAPhi :: Show asn => SSAPhi asn (Term AVal) -> String
ppSSAPhi (_, blks) = show $ IntMap.foldWithKey
                  (\ i (phi, defs, exit) doc ->
                    text (".l" ++ show i) $+$
                    nest 4 (vcat $
                            map (\(a, phi) ->
                                  text (show a) <+> text "<- phi" <+>
                                  text (show phi))
                            $ Map.assocs phi)
                    $+$
                    nest 4 (vcat (map ppDefine defs) $+$
                            ppExit exit) $+$ doc)
                  (text "")
                  blks

ppExit :: (Show lbl, Show val) => Exit lbl (Term val) -> Doc
ppExit (IfElseGoto e l1 l2) =
  text "if" <+>
  parens (ppTerm (fmap (parens . text . show) e))
  <+> text "then goto" <+> text (".l" ++ show l1)
  <+> text "else goto" <+> text (".l" ++ show l2)
ppExit (Goto lbl) = text "goto" <+> text (".l" ++ show lbl)
ppExit (Return exp) = text "return" <+>
                      parens (ppTerm (fmap (parens . text . show) exp))

assemble :: Blocks (Size, ALoc) (Term AVal) -> SymbolGen [Instr AVal]
assemble (i, blks) = -- trace (ppBlocks (i,blks)) $
  do
    result <- IntMap.foldWithKey
              (\ i e rest -> do
                  asm <- translateAsm i e
                  rest' <- rest
                  return $ asm ++ rest')
              (return [])
              blks
    return (JMP (".l" ++ show i) : result)
                      

translateAsm :: Int -> ([Define (Size, ALoc) (Term AVal)], Exit Int (Term AVal))
             -> SymbolGen [Instr AVal]
translateAsm i (defs, exit) = do
  let defIns = concatMap translateDefine defs
  exitIns <- translateExit exit
  return $ [Label (".l" ++ show i)] ++ defIns ++ exitIns


translateExit :: Exit Int (Term AVal) -> SymbolGen [Instr AVal]
translateExit (Return exp) = return $
                             translateDefine (Define (Q, AReg 0) exp)
                             ++ [RET]
translateExit (Goto lbl) = return [JMP (".l" ++ show lbl)]
translateExit (IfElseGoto e thn' els') = let
  thn = ".l" ++ show thn'
  els = ".l" ++ show els'
  in
   case e of
     BinOp Eq e1 e2 -> return [CMPL e2 e1, JE thn, JMP els]
     BinOp NEq e1 e2 -> return [CMPL e2 e1, JNE thn, JMP els]
     BinOp Lt e1 e2 -> return [CMPL e2 e1, JL thn, JMP els]
     BinOp LtE e1 e2 -> return [CMPL e2 e1, JLE thn, JMP els]
     BinOp Gt e1 e2 -> return [CMPL e2 e1, JG thn, JMP els]
     BinOp GtE e1 e2 -> return [CMPL e2 e1, JGE thn, JMP els]
     _ -> do
       cond <- newIndex
       trueLoc <- newIndex
       let cond' = ALoc L $ ATemp cond
           trueLoc' = ALoc L $ ATemp trueLoc
       exit <- translateExit (IfElseGoto (BinOp Eq cond' trueLoc') thn' els')
       return $
         translateDefine (Define (L, ATemp cond) e)
         ++ [MOVL (AImm true) (ALoc L $ ATemp trueLoc)]
         ++ exit
            
                       
translateDefine :: Define (Size, ALoc) (Term AVal) -> [Instr AVal]
translateDefine (Define (Aggregate _, a) e) =
  translateDefine (Define (Q, a) e)
translateDefine (Define (s, a) e) =
  case e of
    BinOp Add b c
      | ALoc _ b' <- b, b' == a -> [ADDL c (ALoc s a)]
      | ALoc _ c' <- c, c' == a -> [ADDL b (ALoc s a)]
      | otherwise -> [MOVL b (ALoc s a),
                     ADDL c (ALoc s a)]
    BinOp Sub b c
      | ALoc _ b' <- b, b' == a -> [SUBL c (ALoc s a)]
      | ALoc _ c' <- c, c' == a -> [NEGQ (ALoc s a),
                                 ADDL b (ALoc s a)]
      | otherwise -> [MOVL b (ALoc s a),
                     SUBL c (ALoc s a)]
    BinOp Mul b c 
      | ALoc _ b' <- b, b' == a -> [IMULL c (ALoc s a)]
      | ALoc _ c' <- c, c' == a -> [IMULL b (ALoc s a)]
      | otherwise -> [MOVL b (ALoc s a),
                     IMULL c (ALoc s a)]
    BinOp Div b c -> [MOVL b (ALoc L $ AReg 0),
                     CLTD,
                     IDIVL c,
                     MOVL (ALoc L $ AReg 0) (ALoc s a)]
    UnOp Neg b -> [MOVL b (ALoc s a), NEGQ (ALoc s a)]
    BinOp Mod b c -> [MOVL b (ALoc L $ AReg 0),
                     CLTD,
                     IDIVL c,
                     MOVL (ALoc L $ AReg 2) (ALoc s a)]
    UnOp Nop b -> [MOVL b (ALoc s a)]
    UnOp Not b ->  [MOVL b (ALoc L a),
                   NOTL (ALoc L a),
                   ANDL (AImm 1) (ALoc L a)]
    UnOp Comp b -> [MOVL b (ALoc s a),
                  NOTL (ALoc s a)]
    BinOp Lt b c -> [MOVL (AImm false) (ALoc s a),
                    CMPL c b,
                    CMOVL (AImm true) (ALoc s a)
                   ]
    BinOp LtE b c -> [MOVL (AImm false) (ALoc s a),
                     CMPL c b,
                     CMOVLE (AImm true) (ALoc s a)
                    ]
    BinOp Gt b c -> [MOVL (AImm false) (ALoc s a),
                    CMPL c b,
                    CMOVG (AImm true) (ALoc s a)
                   ]
    BinOp GtE b c -> [MOVL (AImm false) (ALoc s a),
                     CMPL c b,
                     CMOVGE (AImm true) (ALoc s a)
                    ]
    BinOp Eq b c -> [MOVL (AImm false) (ALoc s a),
                    CMPL c b,
                    CMOVE (AImm true) (ALoc s a)
                   ]
    BinOp NEq b c -> [MOVL (AImm false) (ALoc s a),
                     CMPL c b,
                     CMOVNE (AImm true) (ALoc s a)
                    ]
    BinOp AND b c -> [MOVL b (ALoc s a),
                     ANDL c (ALoc s a)
                    ]
    BinOp XOR b c -> [MOVL b (ALoc s a),
                     XORL c (ALoc s a)
                    ]
    BinOp OR b c -> [MOVL b (ALoc s a),
                    ORL c (ALoc s a)
                   ]
    BinOp SL b c -> [MOVL b (ALoc s a),
                    SALL c (ALoc s a)
                   ]
    BinOp SR b c -> [MOVL b (ALoc s a),
                    SARL c (ALoc s a)
                   ]
    Call f params ->
      let indexedParams = reverse $ zip [1..] params
          save (i, p) = MOVL p (ALoc Q $ AArg i)
          store = fmap save indexedParams
      in
        store ++ [MOVL (AImm 0) (ALoc Q (AReg 0)),
                  CALL f params,
                  MOVL (ALoc Q (AReg 0)) (ALoc s a)
                 ]


-- LLVM 
{-
toType :: Size -> LLVM.Type
toType B = LLVM.IntegerType 8
toType S = LLVM.IntegerType 16
toType L = LLVM.IntegerType 32
toType Q = LLVM.IntegerType 64
toType t = error $ "Unknown type " ++ show t

operand :: AVal -> SymbolGen ([LLVM.Named LLVM.Instruction], LLVM.Operand)
operand (AImm i) = return ([], LLVM.ConstantOperand $
                               LLVMC.Int 32 (fromIntegral i))
operand (ALoc s (ATemp i)) =
  return ([], LLVM.LocalReference (Name $ "t" ++ show i))
operand (ALoc s (AAddr v)) = do
  (rest, v') <- operand v
  i <- newIndex
  j <- newIndex
  let i' = LLVM.UnName $ fromIntegral i
      j' = LLVM.UnName $ fromIntegral j
      pointerType = LLVM.PointerType (toType s) (AddrSpace 0)
  return (rest ++
          [i' := (LLVM.IntToPtr v' pointerType []),
           j' := (LLVM.Load False (LLVM.LocalReference i') Nothing 0 [])],
          LLVM.LocalReference j')
operand (ALoc s (AOffset o v)) = do
  (rest, v') <- operand v
  i <- newIndex
  j <- newIndex
  k <- newIndex
  let i' = LLVM.UnName $ fromIntegral i
      j' = LLVM.UnName $ fromIntegral j
      k' = LLVM.UnName $ fromIntegral k
      offset = LLVM.ConstantOperand $
               LLVMC.Int 64 (fromIntegral o)
      pointerType = LLVM.PointerType (toType s) (AddrSpace 0)
  return (rest ++
          [i' := (LLVM.Add False False v' offset []), 
           j' := (LLVM.IntToPtr (LLVM.LocalReference i') pointerType []),
           k' := (LLVM.Load False (LLVM.LocalReference j') Nothing 0 [])],
          LLVM.LocalReference k')
operand (ALoc s (AIndex o v x s')) = do
  (restv, v') <- operand v
  (restx, x') <- operand x 
  i <- newIndex
  j <- newIndex
  k <- newIndex
  m <- newIndex
  n <- newIndex
  let i' = LLVM.UnName $ fromIntegral i
      j' = LLVM.UnName $ fromIntegral j
      k' = LLVM.UnName $ fromIntegral k
      m' = LLVM.UnName $ fromIntegral m
      n' = LLVM.UnName $ fromIntegral n
      offset = LLVM.ConstantOperand $
               LLVMC.Int 64 (fromIntegral o)
      size = LLVM.ConstantOperand $
             LLVMC.Int 64 (fromIntegral $ bytes s')
      pointerType = LLVM.PointerType (toType s) (AddrSpace 0)
  return (restv ++ restx ++
          [i' := (LLVM.Mul False False x' size []),
           j' := (LLVM.Add False False (LLVM.LocalReference i') v' []),
           k' := (LLVM.Add False False (LLVM.LocalReference j') offset []),
           m' := (LLVM.IntToPtr (LLVM.LocalReference k') pointerType []),
           n' := (LLVM.Load False (LLVM.LocalReference m') Nothing 0 [])],
          LLVM.LocalReference n')

llvmTerm :: Set String
         -> Term AVal
         -> SymbolGen ([LLVM.Named LLVM.Instruction],
                       LLVM.Instruction)
llvmTerm _ (BinOp o b c) = do
  (initb, b') <- operand b
  (initc, c') <- operand c
  let op = case o of
        Add -> LLVM.Add False False
        Sub -> LLVM.Sub False False
        Mul -> LLVM.Mul False False
        Div -> LLVM.SDiv False
        Mod -> LLVM.SRem
        Lt -> LLVM.ICmp SLT
        LtE -> LLVM.ICmp SLE
        Gt -> LLVM.ICmp SGT
        GtE -> LLVM.ICmp SGE
        Eq -> LLVM.ICmp EQ
        NEq -> LLVM.ICmp NE
        AND -> LLVM.And
        OR -> LLVM.Or
        XOR -> LLVM.Xor
        SL -> LLVM.Shl False False
        SR -> LLVM.AShr False
  return (initb ++ initc, op b' c' [])
llvmTerm _ (UnOp o b) = do
  (initb, b') <- operand b
  let zero = LLVM.ConstantOperand $ LLVMC.Int 32 0
      neg1 = LLVM.ConstantOperand $ LLVMC.Int 32 (-1)
      one = LLVM.ConstantOperand $ LLVMC.Int 32 1
  case o of
    Neg -> return (initb, LLVM.Sub False False zero b' [])
    Nop -> return (initb, LLVM.Add False False zero b' [])
    Comp -> return (initb, LLVM.Xor neg1 b' [])
    Not -> do
      i <- newIndex
      let i' = UnName $ fromIntegral i
      return (initb ++
              [i' := (LLVM.Xor neg1 b' [])],
              LLVM.And one (LLVM.LocalReference i') [])
llvmTerm fns (Call f params) = do
  let f' = if Set.member f fns
           then LLVM.ConstantOperand $
                LLVMC.GlobalReference $ Name ("_c0_" ++ f)
           else LLVM.ConstantOperand $
                LLVMC.GlobalReference $ Name f
  params' <- mapM operand params
  let (init, params'') = unzip params'
  return (concat init,
          LLVM.Call False C [] (Right f') (map (flip (,) []) params'') [] [])

llvmDefine :: Set String
           -> Define (Size, ALoc) (Term AVal)
           -> SymbolGen [LLVM.Named LLVM.Instruction]
llvmDefine fns (Define (Aggregate _, a) e) =
  llvmDefine fns (Define (Q, a) e)
llvmDefine fns (Define (s, a) e) = do
  (init, instr) <- llvmTerm fns e
  case a of
    ATemp i -> return $ init ++ [Name ("t" ++ show i) := instr]
    AAddr v ->  do
      (rest, v') <- operand v
      i <- newIndex
      j <- newIndex
      let i' = LLVM.UnName $ fromIntegral i
          j' = LLVM.UnName $ fromIntegral j
          pointerType = LLVM.PointerType (toType s) (AddrSpace 0)
      return $ init ++ rest ++ 
        [i' := (LLVM.IntToPtr v' pointerType []),
         j' := instr,
         Do (LLVM.Store False (LLVM.LocalReference i')
             (LLVM.LocalReference j') Nothing 0 [])]
    AOffset o v -> do
      (rest, v') <- operand v
      i <- newIndex
      j <- newIndex
      k <- newIndex
      let i' = LLVM.UnName $ fromIntegral i
          j' = LLVM.UnName $ fromIntegral j
          k' = LLVM.UnName $ fromIntegral k
          offset = LLVM.ConstantOperand $
                   LLVMC.Int 64 (fromIntegral o)
          pointerType = LLVM.PointerType (toType s) (AddrSpace 0)
      return $ init ++ rest ++
        [i' := (LLVM.Add False False v' offset []), 
         j' := (LLVM.IntToPtr (LLVM.LocalReference i') pointerType []),
         k' := instr,
         Do (LLVM.Store False (LLVM.LocalReference j')
             (LLVM.LocalReference k') Nothing 0 [])]
    AIndex o v x s -> do
      (restv, v') <- operand v
      (restx, x') <- operand x 
      i <- newIndex
      j <- newIndex
      k <- newIndex
      m <- newIndex
      n <- newIndex
      let i' = LLVM.UnName $ fromIntegral i
          j' = LLVM.UnName $ fromIntegral j
          k' = LLVM.UnName $ fromIntegral k
          m' = LLVM.UnName $ fromIntegral m
          n' = LLVM.UnName $ fromIntegral n
          offset = LLVM.ConstantOperand $
                   LLVMC.Int 64 (fromIntegral o)
          size = LLVM.ConstantOperand $
                 LLVMC.Int 64 (fromIntegral $ bytes s)
          pointerType = LLVM.PointerType (toType s) (AddrSpace 0)
      return $ init ++ restv ++ restx ++
        [i' := (LLVM.Mul False False x' size []),
         j' := (LLVM.Add False False (LLVM.LocalReference i') v' []),
         k' := (LLVM.Add False False (LLVM.LocalReference j') offset []),
         m' := (LLVM.IntToPtr (LLVM.LocalReference k') pointerType []),
         n' := instr,
         Do (LLVM.Store False (LLVM.LocalReference m')
             (LLVM.LocalReference n') Nothing 0 [])]

llvmBlock :: Set String -> Int
          -> SSAPhiBlock (Size, ALoc) (Term AVal)
          -> SymbolGen LLVM.BasicBlock
llvmBlock fns i (phi, defs, exit) = do
  let toIncoming ((s, a), i) = do
        (init, asn') <- operand $ ALoc s a
        case init of
          [] -> return ()
          _ -> error $ "Label .l" ++ show i ++ " parameterized with heap value."
        return (asn', Name $ ".l" ++ show i)
  phi' <- mapM (mapM toIncoming) phi
  let phi'' = Map.assocs phi'
      toInstr ((s, a), incoming) =
        case a of
          ATemp i ->
            (Name ("t" ++ show i) := (LLVM.Phi (toType s) incoming []))
          _ -> error $ "Label .l" ++ show i ++ " parameterized with heap value."
  defs' <- mapM (llvmDefine fns) defs
  (rest, exit') <- case exit of
    Return e -> do
      (rest, e') <- llvmTerm fns e
      i <- newIndex
      let i' = UnName $ fromIntegral i
      return (rest ++ [i' := e'],
              LLVM.Ret (Just $ LLVM.LocalReference i') [])
    Goto lbl -> return ([], LLVM.Br (Name $ ".l" ++ show lbl) [])
    IfElseGoto e lbl1 lbl2 -> do
      (rest, e') <- llvmTerm fns e
      i <- newIndex
      let i' = UnName $ fromIntegral i
      return (rest ++ [i' := e'],
              LLVM.CondBr (LLVM.LocalReference i')
              (Name $ ".l" ++ show lbl1)
              (Name $ ".l" ++ show lbl2)
              [])
  let defs'' = map toInstr phi'' ++ concat defs' ++ rest
  return $ LLVM.BasicBlock (Name $ ".l" ++ show i) defs'' (Do exit')

llvmFn :: Set String -> String
       -> ([AVal], Size, SSAPhi (Size, ALoc) (Term AVal))
       -> LLVM.Definition
llvmFn fns fn (params, size, (start, blks)) = allocate $ do
  let combine i blk rest = do
        rest' <- rest
        result <- llvmBlock fns i blk
        return $ result : rest'
  blks' <- IntMap.foldrWithKey combine (return []) blks
  i <- newIndex
  let i' = UnName $ fromIntegral i
      start' = LLVM.BasicBlock i' []
               (Do $ LLVM.Br (Name $ ".l" ++ show start) [])
      body = start' : blks'
      getParam (ALoc s (ATemp i)) = LLVM.Parameter (toType s)
                                    (Name ("t" ++ show i)) []
      getParam s = error $ show s ++ " is not a temporary variable."
      params' = map getParam params
      fn' = LLVM.functionDefaults
            { returnType = toType size
            , name = Name $ "_c0_" ++ fn
            , parameters = (params', False)
            , basicBlocks = body
            }
  return $ LLVM.GlobalDefinition fn'
-}

-- LLVM IR

toType' :: Size -> Doc
toType' B = text "i1"
toType' S = text "i16"
toType' L = text "i32"
toType' Q = text "i64"
toType' t = error $ "Unknown type " ++ show t

operand' :: AVal -> SymbolGen (Doc, Doc)
operand' (AImm i) = return (empty, text (show i))
operand' (ALoc s (AReg i)) = return (empty, text $ "%r" ++ show i)
operand' (ALoc s (ATemp i)) = 
  return (empty, text $ "%t" ++ show i)
operand' (ALoc s (AAddr v)) = do
  (rest, v') <- operand' v
  i <- newIndex
  j <- newIndex
  let i' = text $ "%u" ++ show i
      j' = text $ "%u" ++ show j
      pointerType = toType' s <> text "*"
  return (rest $+$ vcat
          [i' <+> text "=" <+> text "inttoptr" <+>
           (toType' Q) <+> v' <+> text "to" <+> pointerType,
           j' <+> text "=" <+> text "load" <+> pointerType <+> i'],
          j')
operand' (ALoc s (AOffset o v)) = do
  (rest, v') <- operand' v
  i <- newIndex
  j <- newIndex
  k <- newIndex
  let i' = text $ "%u" ++ show i
      j' = text $ "%u" ++ show j
      k' = text $ "%u" ++ show k
      offset = text $ show o
      pointerType = toType' s <> text "*"
  return (rest $+$ vcat
          [i' <+> text "=" <+> text "add i64" <+> v' <> comma <+> offset,
           j' <+> text "=" <+> text "inttoptr" <+>
           (toType' Q) <+> i' <+> text "to" <+> pointerType,
           k' <+> text "=" <+> text "load" <+> pointerType <+> j'],
          k')
operand' (ALoc s (AIndex o v x s')) = do
  (restv, v') <- operand' v
  (restx, x') <- operand' x 
  i <- newIndex
  j <- newIndex
  k <- newIndex
  m <- newIndex
  n <- newIndex
  let i' = text $ "%u" ++ show i
      j' = text $ "%u" ++ show j
      k' = text $ "%u" ++ show k
      m' = text $ "%u" ++ show m
      n' = text $ "%u" ++ show n
      offset = text $ show o
      size = text $ show $ bytes s'
      pointerType = toType' s <> text "*"
  return (restv $+$ restx $+$ vcat
          [i' <+> text "=" <+> text "mul i64" <+> x' <> comma <+> size,
           j' <+> text "=" <+> text "add i64" <+> i' <> comma <+> v',
           k' <+> text "=" <+> text "add i64" <+> j' <> comma <+> offset,
           m' <+> text "=" <+> text "inttoptr" <+>
           (toType' Q) <+> k' <+> text "to" <+> pointerType,
           n' <+> text "=" <+> text "load" <+> pointerType <+> m'],
          n')
operand' x = error $ show x

convertSize :: Size -> Size -> Doc -> SymbolGen (Doc, Doc)
convertSize s s' e = do
  if s == s'
    then return (empty, e)
    else if s < s' then do
    i <- newIndex
    let i' = text $ "%u" ++ show i
    return (i' <+> text "=" <+> e,
            text "sext" <+> toType' s <+> i'
            <+> text "to" <+> toType' s')
         else do
           i <- newIndex
           let i' = text $ "%u" ++ show i
           return (text "; Seg Fault" $+$ i' <+> text "=" <+> e,
                   text "trunc" <+> toType' s <+> i'
                   <+> text "to" <+> toType' s')

convert :: Size -> Size -> Doc -> SymbolGen (Doc, Doc)
convert s s' e = do
  if s == s'
    then return (empty, e)
    else if s < s' then do
    i <- newIndex
    let i' = text $ "%u" ++ show i
    return (i' <+> text "=" <+>
            text "sext" <+> toType' s <+> e
            <+> text "to" <+> toType' s',
            i')
         else do
           i <- newIndex
           let i' = text $ "%u" ++ show i
           return (text "; Seg Fault" $+$
                   i' <+> text "=" <+>
                   text "trunc" <+> toType' s <+> e
                   <+> text "to" <+> toType' s',
                   i')

llvmTerm' :: Set String
          -> Size 
          -> Term AVal
          -> SymbolGen (Doc, Doc)
llvmTerm' _ s (BinOp o b c)
  | o `elem` [Lt, LtE, Gt, GtE, Eq, NEq] = do
    (initb, b') <- operand' b
    (initc, c') <- operand' c
    let op = case o of
          Lt -> text "icmp slt"
          LtE -> text "icmp sle"
          Gt -> text "icmp sgt"
          GtE -> text "icmp sge"
          Eq -> text "icmp eq"
          NEq -> text "icmp ne"
        size1 = case b of
          ALoc s _ -> s
          _ -> L
        size2 = case c of
          ALoc s _ -> s
          _ -> L
        size = max size1 size2
    (resize1, arg1) <- convert size1 size b'
    (resize2, arg2) <- convert size2 size c'
    {-(resize, result) <- convertSize size s $
                        op <+> (toType' size) <+> b' <> comma <+> c'
    return (initb $+$ initc $+$ resize, result)-}
    i <- newIndex
    let i' = text $ "%u" ++ show i
    if s == B then
      return (initb $+$ initc $+$ resize1 $+$ resize2,
              op <+> (toType' size) <+> arg1 <> comma <+> arg2)
      else
      return (initb $+$ initc $+$ resize1 $+$ resize2 $+$
              i' <+> text "=" <+> op <+> (toType' size) <+> arg1 <>
              comma <+> arg2,
              text "sext" <+> text "i1" <+> i'
              <+> text "to" <+> (toType' s))
  | otherwise = do
    (initb, b') <- operand' b
    (initc, c') <- operand' c
    let op = case o of
          Add -> text "add"
          Sub -> text "sub"
          Mul -> text "mul"
          Div -> text "sdiv"
          Mod -> text "srem"
          AND -> text "and"
          OR -> text "or"
          XOR -> text "xor"
          SL -> text "shl"
          SR -> text "ashr"
        size = case (b, c) of
          (ALoc s1 _, ALoc s2 _) -> max s1 s2
          (ALoc s _, _) -> s
          (_, ALoc s _) -> s
          (_, _) -> L
    (resize, result) <- convertSize size s $
                        op <+> (toType' size) <+> b' <> comma <+> c'
    return (initb $+$ initc $+$ resize, result)
llvmTerm' _ s (UnOp o b) = do
  (initb, b') <- operand' b
  let zero = text "0"
      neg1 = text "-1"
      one = text "1"
      size = case b of
        AImm _ -> L
        ALoc s _ -> s
  case o of
    Neg -> do
      (resize, result) <- convertSize size s $
                          text "sub" <+> toType' size <+> zero <> comma <+> b'
      return (initb $+$ resize, result)
    Nop -> do
      (resize, result) <- convertSize size s $
                          text "add" <+> toType' size <+> b' <> comma <+> zero
      return (initb $+$ resize, result)
    Comp -> do
      (resize, result) <- convertSize size s $
                          text "xor" <+> toType' size <+> neg1 <> comma <+> b'
      return (resize, result) 
    Not -> do
      i <- newIndex
      let i' = text $ "%u" ++ show i
      (resize, result) <- convertSize size s $
                          text "and" <+> toType' size <+> one <> comma <+> i'
      return (initb $+$
              (i' <+> text "=" <+> text "xor" <+> toType' size
               <+> neg1 <> comma <+> b') $+$ resize,
              result)
llvmTerm' fns s (Call f params) = do
  let f' = if Set.member f fns
           then text $ "@_c0_" ++ f
           else text $ "@" ++ f
      getSize (AImm _) = L
      getSize (ALoc s _) = s
      sizes = map (toType' . getSize) params
  params' <- mapM operand' params
  let (init, params'') = unzip params'
      paramsWTypes = zip params'' sizes
      params''' = map (\(p, t) -> t <+> p) paramsWTypes
  return (vcat init,
          text "call" <+> toType' s <+> f' <+>
          parens (hsep $ punctuate comma params'''))

llvmDefine' :: Set String
            -> Define (Size, ALoc) (Term AVal)
            -> SymbolGen Doc
llvmDefine' fns (Define (Aggregate _, a) e) =
  llvmDefine' fns (Define (Q, a) e)
llvmDefine' fns (Define (s, a) e) = do
  (init, instr) <- llvmTerm' fns s e
  case a of
    ATemp i -> do
      
      return $ init $+$
               (text ("%t" ++ show i) <+> text "=" <+> instr)
    AReg i -> return $ init $+$
              (text ("%r" ++ show i) <+> text "=" <+> instr)
    AAddr v ->  do
      (rest, v') <- operand' v
      i <- newIndex
      j <- newIndex
      let i' = text $ "%u" ++ show i
          j' = text $ "%u" ++ show j
          pointerType = toType' s <> text "*"
      return $ init $+$ rest $+$ vcat
        [i' <+> text "=" <+> text "inttoptr" <+>
         (toType' Q) <+> v' <+> text "to" <+> pointerType,
         j' <+> text "=" <+> instr,
         text "store" <+> (toType' s) <+> j' <> comma
         <+> pointerType <+> i']
    AOffset o v -> do
      (rest, v') <- operand' v
      i <- newIndex
      j <- newIndex
      k <- newIndex
      let i' = text $ "%u" ++ show i
          j' = text $ "%u" ++ show j
          k' = text $ "%u" ++ show k
          offset = text $ show o
          pointerType = toType' s <> text "*"
      return $ init $+$ rest $+$ vcat
        [i' <+> text "=" <+> text "add i64" <+> v' <> comma <+> offset,
         j' <+> text "=" <+> text "inttoptr" <+>
         (toType' Q) <+> i' <+> text "to" <+> pointerType <+>
         k' <+> text "=" <+> instr,
         text "store" <+> (toType' s) <+> k' <> comma
         <+> pointerType <+> j']
    AIndex o v x s -> do
      (restv, v') <- operand' v
      (restx, x') <- operand' x 
      i <- newIndex
      j <- newIndex
      k <- newIndex
      m <- newIndex
      n <- newIndex
      let i' = text $ "%u" ++ show i
          j' = text $ "%u" ++ show j
          k' = text $ "%u" ++ show k
          m' = text $ "%u" ++ show m
          n' = text $ "%u" ++ show n
          offset = text $ show o
          size = text $ show $ bytes s
          pointerType = toType' s <> text "*"
      return $ init $+$ restv $+$ restx $+$ vcat
        [i' <+> text "=" <+> text "mul i64" <+> x' <> comma <+> size,
         j' <+> text "=" <+> text "add i64" <+> i' <> comma <+> v',
         k' <+> text "=" <+> text "add i64" <+> j' <> comma <+> offset,
         m' <+> text "=" <+> text "inttoptr" <+>
         (toType' Q) <+> k' <+> text "to" <+> pointerType <+>
         n' <+> text "=" <+> instr,
         text "store" <+> (toType' s) <+> n' <> comma
         <+> pointerType <+> m']

llvmBlock' :: Set String -> Size -> Int
           -> SSAPhiBlock (Size, ALoc) (Term AVal)
           -> SymbolGen Doc
llvmBlock' fns s i (phi, defs, exit) = do
  let toIncoming ((s, a), i) = do
        (init, asn') <- operand' $ ALoc s a
        return $ brackets (asn' <> comma <+> text ("%l" ++ show i))
  phi' <- mapM (mapM toIncoming) phi
  let phi'' = Map.assocs phi'
      toInstr ((s, a), incoming) =
        case a of
          ATemp i ->
            text ("%t" ++ show i) <+> text "="
            <+> text "phi" <+> (toType' s) <+>
            hsep (punctuate comma incoming)
          _ -> error $ "Label %l" ++ show i ++ " parameterized with heap value."
  defs' <- mapM (llvmDefine' fns) defs
  (rest, exit') <- case exit of
    Return e -> do
      (rest, e') <- llvmTerm' fns s e
      i <- newIndex
      let i' = text $ "%u" ++ show i
      return (rest $+$ (i' <+> text "=" <+> e'),
              text "ret" <+> (toType' s) <+> i')
    Goto lbl -> return (empty, text "br label" <+> text ("%l" ++ show lbl))
    IfElseGoto e lbl1 lbl2 -> do
      (rest, e') <- llvmTerm' fns B e
      i <- newIndex
      let i' = text $ "%u" ++ show i
      return (rest $+$ (i' <+> text "=" <+> e'),
              text "br i1" <+> i' <> comma <+>
              text "label" <+> text ("%l" ++ show lbl1) <> comma <+>
              text "label" <+> text ("%l" ++ show lbl2))
  let defs'' = vcat (map toInstr phi'') $+$ vcat defs' $+$ rest
  return $ text ("l" ++ show i) <> text ":" $+$
    nest 2 (defs'' $+$ exit')

llvmFn' :: Set String -> String
        -> ([AVal], Size, SSAPhi (Size, ALoc) (Term AVal))
        -> Doc
llvmFn' fns fn (params, size, (start, blks)) = allocate $ do
  let combine i blk rest = do
        rest' <- rest
        result <- llvmBlock' fns size i blk
        return $ result $+$ rest'
  blks' <- IntMap.foldrWithKey combine (return empty) blks
  i <- newIndex
  let i' = text (show i)
      start' = nest 2 $ text "br label" <+> text ("%l" ++ show start)
      body = start' $+$ blks'
      getParam (ALoc s (ATemp i)) = toType' s <+> text ("%t" ++ show i)
      getParam s = error $ show s ++ " is not a temporary variable."
      params' = map getParam params
  return $ text "define" <+> toType' size <+>
    text "@" <> text ("_c0_" ++ fn) <>
    parens (hsep $ punctuate comma $ params')
    <+> lbrace $+$
    nest 2 body
    $+$ rbrace

{-

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
-}
