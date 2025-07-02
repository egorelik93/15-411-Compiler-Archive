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

inline :: Map Ident ([VarDecl Ident],TStmt Ident)
       -> Map Ident ([VarDecl Ident],TStmt Ident)
inline fns = let
  search (FM.Pure e) = FM.Pure e
  search (FM.Free e) =
    case runEnvT e of
      (t, Call f params) -> let
        params' = map search params
        in
         case Map.lookup f fns of
           Just (argDecls, FMP.Pure e) -> allocate $ do
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
   Map.map (\(args, body) -> (args, replace body)) fns

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
          else let
          asmMap = allocate $ do
            ir <- mapM (translate safe ts) fns
            let codeGenMap (v, s) = do
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
  case res of
    Left msg -> error msg
    Right () -> return ()
  where asmFile = replaceExtension (jobOut job) "s"

gcc :: String -> FilePath -> FilePath -> ErrorT String IO ()
gcc args input output = do
  e <- lift $ system $ "gcc" ++ " " ++ intercalate " "
       [args, "-m64", input, "15411.c", "l3rt.c", "-o", output]
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
