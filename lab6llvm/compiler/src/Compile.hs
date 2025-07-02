{- L1 Compiler
   Author: *[Redacted]
   Modified by: [Redacted]

   Main compiler module; takes a job and compiles it
-}
module Compile
(compile
,Job(..)
,defaultJob
,OF(..)
) where

import Prelude hiding (mapM)
import Data.List(intercalate)
import System.FilePath
import System.Process hiding (env)
import System.Exit

import Control.Monad.Error hiding (mapM)
import Data.Set (Set, union, notMember, member)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List (intersect)
import Data.Sequence (Seq)
import Data.Foldable (toList)
import Data.Traversable (mapM)
import qualified Control.Monad.Free as FM
import qualified Control.MonadOr.Free as FMP
import Control.Comonad.Trans.Env
-- import qualified LLVM.General.AST as LLVM
-- import qualified LLVM.General.AST.Constant as LLVMC
-- import LLVM.General.AST (Named(..))
-- import LLVM.General.AST.Name
-- import LLVM.General.AST.Global
-- import LLVM.General.AST.IntegerPredicate
-- import LLVM.General.AST.CallingConvention
import Text.PrettyPrint.HughesPJ
import Debug.Trace

import Compile.Types hiding (used, defined)
import Compile.Types.Grammar (Program)
import Compile.Parser (parseProgram)
import Compile.TypeChecker
-- import Compile.CheckAST
import Compile.CodeGen
import Compile.Translation
import Compile.Analysis
import Compile.Types.Assembly
import Compile.Types.X86_64 as X86
import Compile.RegisterAllocator
import Compile.Elaboration
import Compile.SymbolGen
import Compile.SSA
import Compile.Optimization

import LiftIOE

writeC0 file obj = liftIOE $ writeFile file $ renderC0 obj
writeAsm file obj = liftIOE $ writeFile file $ renderAsm obj
writer file obj = liftIOE $ writeFile file $ show obj
write file obj = liftIOE $ writeFile file obj

finalize :: Opt -> Set Ident -> [AVal] -> [Instr AVal] -> [Instr X86.Expr]
finalize opt fns params asm =
  [SUBQ (constant finalOffset) (Loc Q $ Reg RSP)]
  ++ (map saveCalleeReg $ zip [1..] needToSave)
  ++ getParams
  ++ concat (map fixDeref (substitute asm'))
  where
    paramAssign = map (\(i, l) -> MOVL (loc (size l) (arg i)) l)
                  $ zip [1..] params
    (alloc, needToSave, asm'') = avalToMemory opt (paramAssign ++ asm)
    asm' = concat $ fmap spilled $
           drop (length paramAssign) asm''
    stackOffset = maximum $ [0] ++ do
      line <- asm'
      let v = used line `union` defined line
      [i | Loc _ (DerefOffset i _) <- Set.toList v]
    saveCalleeReg (i, r) =
      MOVL r $
      Loc Q $ DerefOffset (stackOffset + 8 * i) (Loc Q $ Reg RSP)
    restoreCalleeReg (i, r) =
      MOVL (Loc Q $ DerefOffset (stackOffset + 8 * i) (Loc Q $ Reg RSP)) r
    finalOffset =
      case 16 + fromIntegral stackOffset
           + 8 * (length needToSave + 1) of
        o | o `mod` 16 == 0 -> o + 8
        o | otherwise -> o
    substitute ins = do
      i <- ins
      let boolConstLoc = Loc L (DerefOffset 0 (Loc Q (Reg RSP)))
      case i of
        RET ->
          (map restoreCalleeReg $ zip [1..] needToSave)
          ++ [ADDQ (constant finalOffset) (Loc Q $ Reg RSP),
              RET]
        SALL c a -> [MOVL c (Loc L (Reg ECX)), SALL (Loc L (Reg CL)) a]
        SARL c a -> [MOVL c (Loc L (Reg ECX)), SARL (Loc L (Reg CL)) a]
        CMOVL b l -> [MOVL b boolConstLoc, CMOVL boolConstLoc l]
        CMOVLE b l -> [MOVL b boolConstLoc, CMOVLE boolConstLoc l]
        CMOVG b l -> [MOVL b boolConstLoc, CMOVG boolConstLoc l]
        CMOVGE b l -> [MOVL b boolConstLoc, CMOVGE boolConstLoc l]
        CMOVE b l -> [MOVL b boolConstLoc, CMOVE boolConstLoc l]
        CMOVNE b l -> [MOVL b boolConstLoc, CMOVNE boolConstLoc l]
        MOVL i j | i == j -> []
        CALL f p | Set.member f fns -> [CALL ("_c0_" ++ f) p]
        _ -> return i
    fixDeref :: X86.Instr X86.Expr -> [X86.Instr X86.Expr]
    fixDeref i = getAddress ++ [fmap substitute i]
      where
        vars = Set.union (used i) (defined i)
        badVar (Loc _ (DerefIndex _ _ (Loc _ (DerefOffset _ _)) _)) = True
        badVar (Loc _ (DerefOffset _ (Loc _ (DerefOffset _ _)))) = True
        badVar (Loc _ (X86.Deref (Loc _ (DerefOffset _ _)))) = True
        badVar (Loc _ (DerefIndex _ (Loc _ (DerefOffset _ _)) _ _)) = True
        badVar _ = False 
        offsetVars = Set.toList $ Set.filter badVar vars
        getAddress = do
          v <- offsetVars
          case v of
            Loc s (DerefIndex o x i s'') ->
              [MOVL i (Loc Q $ Reg R10D),
               IMULL (Const $ fromIntegral $ bytes s'') (Loc Q $ Reg R10D),
               ADDL x (Loc Q $ Reg R10D)
              ]
            Loc s (X86.Deref (Loc s' (DerefOffset o' b))) ->
              fixDeref (MOVL (Loc s' $ DerefOffset o' b) (Loc s' $ Reg R10D))
            Loc s (DerefOffset o (Loc s' (DerefOffset o' b))) ->
              fixDeref (MOVL (Loc s' $ DerefOffset o' b) (Loc s' $ Reg R10D))
        substitute l@(Loc s (DerefIndex o _ _ _)) | badVar l =
          Loc s (DerefOffset o (Loc Q $ Reg R10D))
        substitute (Loc s (X86.Deref (Loc s' (DerefOffset o' b)))) =
          Loc s (X86.Deref (Loc s' (Reg R10D)))
        substitute (Loc s (DerefOffset o (Loc s' (DerefOffset o' b)))) =
          Loc s (DerefOffset o (Loc s' (Reg R10D)))
        substitute x = x
    arg' s i = case arg i of
      Reg r -> Loc s (Reg r)
      DerefOffset o r ->
        Loc s (DerefOffset (o + fromIntegral finalOffset + 8) r)
      l -> loc s l
    indexedParams = zip [1 ..] params
    getParams = concat $ fmap spilled $
                concat $ map (\(i, ALoc s l) ->
                               case Map.lookup l alloc of
                                 Just l' -> [MOVL (arg' s i) (loc s l')]
                                 Nothing -> []
                             ) indexedParams

inline :: Map Ident ([VarDecl Ident], C0Type Ident, TStmt Ident)
       -> Map Ident ([VarDecl Ident], C0Type Ident, TStmt Ident)
inline fns = let
  search (FM.Pure e) = FM.Pure e
  search (FM.Free e) =
    case runEnvT e of
      (t, Call f params) -> let
        params' = map search params
        in
         case Map.lookup f fns of
           Just (argDecls, _, FMP.Pure e) -> allocate $ do
             newIndices <- mapM (\_ -> newIndex) params'
             let argsWNew = zip argDecls newIndices
                 substVar (VarDecl t id _, v) e =
                   substExpr (FM.Pure $ env t $ VarVal $ show v)
                   id e
                 e' = foldr substVar e argsWNew
                 substParam (param, i) e =
                   substExpr param (show i) e
                 paramsWNew = zip params' newIndices
                 e'' = foldr substParam e' paramsWNew
             return $ search e''
           _ -> FM.Free $ EnvT t $ Call f params'
      _ -> FM.Free $ fmap search e
  replace (FMP.Pure e) = FMP.Pure $ search e
  replace (FMP.Plus ss) = FMP.Plus $ map replace ss
  replace (FMP.Free s) = FMP.Free $
    case s of
      Declare v s' -> Declare v $ replace s'
      Assign l e -> Assign l $ search e
      If e s1 s2 -> If (search e) (replace s1) (replace s2)
      While e blk -> While (search e) (replace blk)
      Eval e -> Eval $ search e
      Assert e -> Assert $ search e
  in
   Map.map (\(args, out, body) -> (args, out, replace body)) fns

llvmDeclare' :: String -> C0Type Ident -> Doc
llvmDeclare' fn (FnType params out) =
  let out' = toType' (sizeOf out)
      params' = map (toType' . sizeOf) params
      decls = zip params' [0 ..]
      toParam (t, a) = t <+> text ("%a" ++ show a)
  in
   text "declare" <+> out' <+> text ("@" ++ fn) <+>
   parens (hsep $ punctuate comma $ map toParam decls)

compile :: Job -> IO ()
compile job = do
  res <- runErrorT $ do
    (ts, link) <- if jobLink job /= ""
            then parseProgram [] $ jobLink job
            else return ([], [])
    (_, prog) <- parseProgram ts $ jobSource job
                 :: ErrorT String IO ([Ident], Program)
    case (elaborate prog, elaborate link) of
      (Left e, _) -> error (show e)
      (_, Left e) -> error (show e)
      (Right ast, Right link) -> do
        (ts, ctx) <- case checkAST link of
          Left (TypeError e) -> throwError ("Type Error: " ++ e)
          Left (ErrorMsg e) -> throwError e
          Left (UndefinedVar _ _ e) -> throwError e
          Right (ts, ctx, _) -> return (ts, ctx)
        -- lift $ putStrLn $ renderC0 ast
        (ts, fns') <- case checkTopLevel ts ctx ast of
          Left (TypeError e) -> throwError ("Type Error: " ++ e)
          Left (ErrorMsg e) -> throwError e
          Left (UndefinedVar _ _ e) -> throwError e
          Right (ts, _, fns) -> return (ts, fns)
        -- let ast' = stripSourcePos ast
        --     definedFns = Map.keys fns
        -- lift $ putStrLn $ show definedFns
        let safe = jobSafe job
            opt = jobOpt job
                  -- if safe then O0
                  -- else jobOpt job
            fns = case opt of
              O2 -> inline fns'
              _ -> fns'
        case intersect (Map.keys ctx) (Map.keys fns) of
          intersectFns | intersectFns == ["main"] -> return ()
                       | otherwise -> throwError $
                                      "Header functions " ++ show intersectFns
                                      ++ " defined in file"
        if jobOutFormat job == C0
          then writeC0 (jobOut job) ast
          else
          case jobBackend job of
            X86_64 -> let
              asmMap = allocate $ do
                ir <- mapM (translate safe ts) fns
                let codeGenMap (v, size, s) = do
                      asm <- codeGen (Return (UnOp Nop $ AImm 0)) s
                      optAsm <- case opt of
                        O0 -> return asm
                        O1 -> do
                          ssa <- toSSA asm
                          let optSSA = constCopyPropagate ssa
                              reducedSSA = elimDeadCode optSSA
                          asm' <- deSSA reducedSSA
                          return asm'
                        O2 -> do
                          ssa <- toSSA asm
                          let optSSA = constCopyPropagate ssa
                              reducedSSA = elimDeadCode optSSA
                          asm' <- deSSA reducedSSA
                          return asm'
                      x86 <- assemble optAsm
                      return (v, x86)
                mapM codeGenMap ir
              assembleStmt id (l, asm) = (Label ("_c0_" ++ id)) : asm'
                where
                  asm' :: [Instr X86.Expr]
                  asm' = finalize opt (Map.keysSet fns) l asm
              asmMap' = Map.mapWithKey assembleStmt asmMap
              asm = concat $ Map.elems asmMap'
              globl = intercalate "\n" $
                      map (\i -> ".globl _c0_" ++ i) $ Map.keys fns
              asmCode = globl ++ "\n" ++ renderAsm asm
              in
               if jobOutFormat job == Asm
               then do
                 -- lift $ putStrLn $ renderAsm asm'
                 write (jobOut job) asmCode
               else do write asmFile asmCode
                       let o = if jobOutFormat job == Obj then "-c" else ""
                       gcc o asmFile (jobOut job)
            LLVM -> let
              ssaPhiMap = allocate $ do
                ir <- mapM (translate safe ts) fns
                let codeGenMap (v, size, s) = do
                      asm <- codeGen (Return (UnOp Nop $ AImm 0)) s
                      ssa <- toSSA asm
                      let ssa' = case opt of
                            O0 -> ssa
                            O1 -> constCopyPropagate ssa
                            O2 -> {- elimDeadCode $ -} constCopyPropagate ssa
                          ssaPhi = toSSAPhi ssa'
                      return (v, size, ssaPhi)
                mapM codeGenMap ir
              --llvmMap = Map.mapWithKey (llvmFn $ Map.keysSet fns) ssaPhiMap
              --llvm = Map.elems llvmMap
              --program = LLVM.defaultModule {LLVM.moduleDefinitions = llvm}
              llvmMap = Map.mapWithKey (llvmFn' $ Map.keysSet fns) ssaPhiMap
              llvm = vcat $ Map.elems llvmMap
              header = vcat $ Map.elems $
                       Map.mapWithKey llvmDeclare' ctx
              llvmCode = render (header $+$ llvm)
              calloc = "declare i64 @calloc(i32 %a, i32 %b)\n"
              abort = "declare i32 @abort()\n"
              in write llvmFile (calloc ++ abort ++ llvmCode)
               {-do
                result <- lift $ withContext $ \c ->
                  return (withModuleFromAST c program moduleString)
                out <- result
                lift $ putStrLn out-}
                {-      
                      optAsm <- case opt of
                        O0 -> return asm
                        O1 -> do
                          ssa <- toSSA asm
                          let ssaPhi = toSSAPhi 
                              reducedSSA = elimDeadCode optSSA
                          asm' <- deSSA reducedSSA
                          return asm'
                        O2 -> do
                          ssa <- toSSA asm
                          let optSSA = constCopyPropagate ssa
                              reducedSSA = elimDeadCode optSSA
                          asm' <- deSSA reducedSSA
                          return asm'
                      x86 <- assemble optAsm
                      return (v, x86) -}
  case res of
    Left msg -> error msg
    Right () -> return ()
  where asmFile = replaceExtension (jobOut job) "s"
        llvmFile = replaceExtension (jobOut job) "ll"

gcc :: String -> FilePath -> FilePath -> ErrorT String IO ()
gcc args input output = do
  e <- lift $ system $ "gcc" ++ " " ++ intercalate " "
       [args, "-m64", input, "15411.c", "l4rt.c", "-o", output]
  exitErrorCode $ return (e, "", "")

{-
  exitErrorCode $ readProcessWithExitCode
  "gcc"
  [args, input, "-o", output]
  ""
-}
  where exitErrorCode :: IO (ExitCode, String, String) -> ErrorT String IO ()
        exitErrorCode m = do
          (exitCode, _, msg) <- lift m
          case exitCode of
            ExitSuccess   -> return ()
            ExitFailure n -> throwError $ "Error " ++ (show n) ++ "\n" ++ msg


{-
ppModule :: LLVM.Module -> Doc
ppModule m = vcat $ map ppDefinition $ LLVM.moduleDefinitions m

ppDefinition :: LLVM.Definition -> Doc
ppDefinition (GlobalDefinition g) = text "define" <+> ppGlobal g

ppGlobal :: LLVM.Global -> Doc
ppGlobal f = (ppLLVMType $ returnType f) <+> text "@" <> (ppName $ name f)
             <> parens (hsep $ punctuate comma $
                        map ppParameter $ fst $ parameters f)
             <+> lbrace
             $+$ nest 2 (vcat $ map (ppBasicBlock $ returnType f)
                         $ basicBlocks f)
             $+$ rbrace

ppLLVMType :: LLVM.Type -> Doc
ppLLVMType (LLVM.IntegerType b) = text "i" <> text (show b)

ppName :: Name -> Doc
ppName (Name s) = text s
ppName (UnName i) = text (show i)

ppParameter :: LLVM.Parameter -> Doc
ppParameter (Parameter t n _) = ppLLVMType t <+> text "%" <> ppName n

ppBasicBlock :: LLVM.Type -> LLVM.BasicBlock -> Doc
ppBasicBlock tp (BasicBlock n defs exit) =
  case n of
    UnName _ -> nest 2 $ vcat (map (ppNamed ppInstruction) defs)
                $+$ ppNamed ppTerminator exit
    Name t -> text (t ++ ":") $+$
              nest 2 (vcat (map (ppNamed ppInstruction) defs)
                      $+$ ppNamed (ppTerminator tp) exit)

ppNamed :: (a -> Doc) -> LLVM.Named a -> Doc
ppNamed f (n := i) = ppName n <+> text "=" <+> f i
ppNamed f (Do i) = f i

ppOperand :: LLVM.Operand -> Doc
ppOperand (LLVM.LocalReference n) = text "%" <> ppName n
ppOperand (LLVM.ConstantOperand c) = ppConstant c

ppConstant :: LLVMC.Constant -> Doc
ppConstant (LLVMC.Int t i) = text ("i" ++ show t) <+> text (show i)

ppTerminator :: LLVM.Type -> LLVM.Terminator -> Doc
ppTerminator _ (LLVM.Ret Nothing _) = text "ret void"
ppTerminator tp (LLVM.Ret (Just c) _) = text "ret" <+> ppLLVM tp <+>
                                        ppOperand c
ppTerminator _ (LLVM.Br dest _) = text "br label" <+> text "%" <> ppName dest
ppTerminator _ (LLVM.CondBr cond t f _) = text "br i1" <+> ppOperand cond
                                          <> comma <+> text "label"
                                          <+> text "%" <> ppName t
                                          <> comma <+> text "label"
                                          <+> text "%" <> ppName f

ppInstruction :: LLVM.Instruction -> Doc
ppInstruction (LLVM.Add _ _ a b _) = text "add i64" <+>
                                     ppOperand a <> comma
                                     <+> ppOperand b
ppInstruction (LLVM.Sub _ _ a b _) = text "sub i64" <+>
                                     ppOperand a <> comma
                                     <+> ppOperand b
ppInstruction (LLVM.Mul _ _ a b _) = text "mul i64" <+>
                                     ppOperand a <> comma
                                     <+> ppOperand b
ppInstruction (LLVM.SDiv _ a b _) = text "sdiv i32" <+>
                                     ppOperand a <> comma
                                     <+> ppOperand b
ppInstruction (LLVM.SRem a b _) = text "srem i32" <+>
                                     ppOperand a <> comma
                                     <+> ppOperand b
ppInstruction (LLVM.Shl _ _ a b _) = text "shl i32" <+>
                                     ppOperand a <> comma
                                     <+> ppOperand b
ppInstruction (LLVM.AShr _ a b _) = text "ashr i32" <+>
                                     ppOperand a <> comma
                                     <+> ppOperand b
ppInstruction (LLVM.And a b _) = text "and i32" <+>
                                     ppOperand a <> comma
                                     <+> ppOperand b
ppInstruction (LLVM.Or a b _) = text "or i32" <+>
                                     ppOperand a <> comma
                                     <+> ppOperand b
ppInstruction (LLVM.Xor a b _) = text "xor i32" <+>
                                     ppOperand a <> comma
                                     <+> ppOperand b
ppInstruction (LLVM.Load _ a _ _ _) = text "xor i32" <+>a
                                     ppOperand a <> comma
                                     <+> ppOperand b
                                     
ppInstruction (LLVM.ICmp _ _ a b _) = text "sdiv i32" <+>
                                     ppOperand a <> comma
                                     <+> ppOperand b
-}

