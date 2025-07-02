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
import System.Process
import System.Exit

import Control.Monad.Error hiding (mapM)
import Data.Set (Set, union, notMember, member)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List (intersect)
import Data.Traversable (mapM)
import Debug.Trace

import Compile.Types hiding (used, defined)
import Compile.Types.Grammar (Program)
import Compile.Parser (parseProgram)
import Compile.TypeChecker
-- import Compile.CheckAST
-- import Compile.CodeGen
import Compile.Translation
import Compile.Analysis
import Compile.Types.Assembly
import Compile.Types.X86_64 as X86
import Compile.RegisterAllocator
import Compile.Elaboration

import LiftIOE

writeC0 file obj = liftIOE $ writeFile file $ renderC0 obj
writeAsm file obj = liftIOE $ writeFile file $ renderAsm obj
writer file obj = liftIOE $ writeFile file $ show obj
write file obj = liftIOE $ writeFile file obj

finalize :: Set Ident -> [ALoc] -> [Instr AVal] -> [Instr X86.Expr]
finalize fns params asm = 
  [SUBQ (constant finalOffset) (Loc $ Reg RSP)]
  ++ (map saveCalleeReg $ zip [1..] needToSave)
  ++ getParams
  ++ substitute asm'
  where
    paramAssign = map (\(i, l) -> MOVL (arg i) (ALoc l)) $ zip [1..] params
    (alloc, needToSave, asm'') = avalToMemory (paramAssign ++ asm)
    asm' = concat $ fmap spilled $
           drop (length paramAssign) asm''
    stackOffset = maximum $ [0] ++ do
      line <- asm'
      let v = used line `union` defined line
      [i | Loc (DerefOffset i _) <- Set.toList v]
    saveCalleeReg (i, r) =
      MOVL r $
      Loc $ DerefOffset (stackOffset + 8 * i) (Loc $ Reg RSP)
    restoreCalleeReg (i, r) =
      MOVL (Loc $ DerefOffset (stackOffset + 8 * i) (Loc $ Reg RSP)) r
    finalOffset =
      case 16 + fromIntegral stackOffset
           + 8 * (length needToSave + 1) of
        o | o `mod` 16 == 0 -> o + 8
        o | otherwise -> o
    substitute ins = do
      i <- ins
      let boolConstLoc = Loc (DerefOffset 0 (Loc (Reg RSP)))
      case i of
        RET ->
          (map restoreCalleeReg $ zip [1..] needToSave)
          ++ [ADDQ (constant finalOffset) (Loc $ Reg RSP),
              RET]
        SALL c a -> [MOVL c (Loc (Reg ECX)), SALL (Loc (Reg CL)) a]
        SARL c a -> [MOVL c (Loc (Reg ECX)), SARL (Loc (Reg CL)) a]
        CMOVL b l -> [MOVL b boolConstLoc, CMOVL boolConstLoc l]
        CMOVLE b l -> [MOVL b boolConstLoc, CMOVLE boolConstLoc l]
        CMOVG b l -> [MOVL b boolConstLoc, CMOVG boolConstLoc l]
        CMOVGE b l -> [MOVL b boolConstLoc, CMOVGE boolConstLoc l]
        CMOVE b l -> [MOVL b boolConstLoc, CMOVE boolConstLoc l]
        CMOVNE b l -> [MOVL b boolConstLoc, CMOVNE boolConstLoc l]
        MOVL i j | i == j -> []
        CALL f p | Set.member f fns -> [CALL ("_c0_" ++ f) p]
        _ -> return i
    arg' i = case arg i of
      Loc (Reg r) -> Loc (Reg r)
      Loc (DerefOffset o r) ->
        Loc (DerefOffset (o + fromIntegral finalOffset + 8) r)
      l -> l
    indexedParams = zip [1 ..] params
    getParams = concat $ fmap spilled $
                concat $ map (\(i, l) ->
                               case Map.lookup l alloc of
                                 Just l' -> [MOVL (arg' i) l']
                                 Nothing -> []
                             ) indexedParams

compile :: Job -> IO ()
compile job = do
  res <- runErrorT $ do
    prog <- parseProgram $ jobSource job :: ErrorT String IO Program
    link <- if jobLink job /= ""
            then parseProgram $ jobLink job
            else return []
    case (elaborate prog, elaborate link) of
      (Left e, _) -> error (show e)
      (_, Left e) -> error (show e)
      (Right ast, Right link) -> do
        (ts, ctx) <- case checkAST link of
          Left (TypeError e) -> throwError ("Type Error: " ++ e)
          Left (ErrorMsg e) -> throwError e
          Left (UndefinedVar _ _ e) -> throwError e
          Right (ts, ctx) -> return (ts, ctx)
        -- lift $ putStrLn $ renderC0 ast
        case checkTopLevel ts ctx ast of
          Left (TypeError e) -> throwError ("Type Error: " ++ e)
          Left (ErrorMsg e) -> throwError e
          Left (UndefinedVar _ _ e) -> throwError e
          Right _ -> return ()
        let ast' = stripSourcePos ast
            definedFns = [id | FnDef (VarDecl _ id _) _ _ <- ast']
        -- lift $ putStrLn $ show definedFns
        if intersect (Map.keys ctx) definedFns /= ["main"]
          then throwError ("Header functions defined in file")
          else return ()
        if jobOutFormat job == C0
          then writeC0 (jobOut job) ast
          else let
          asmMap = allocate $ do
            ir <- translate ast'
            let codeGenMap (l, s) = do
                  asm <- codeGen s
                  return (l, asm)
            mapM codeGenMap ir
          fns = Map.keysSet asmMap
          assembleStmt id (l, asm) = (Label ("_c0_" ++ id)) : asm'
            where
              asm' :: [Instr X86.Expr]
              asm' = finalize fns l $ assemble asm
          asmMap' = Map.mapWithKey assembleStmt asmMap
          asm = concat $ Map.elems asmMap'
          globl = intercalate "\n" $
                  map (\i -> ".globl _c0_" ++ i) $ Set.toList fns
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
