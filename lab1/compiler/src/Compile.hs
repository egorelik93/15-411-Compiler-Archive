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

import Data.List(intercalate)
import System.FilePath
import System.Process
import System.Exit

import Control.Monad.Error
import Data.Set (Set, union, notMember)
import qualified Data.Set as Set
import Debug.Trace

import Compile.Types
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

finalize :: [Instr AVal] -> [Instr X86.Expr]
finalize asm = [SUBQ (constant $ 16 + fromIntegral stackOffset) (Loc $ Reg RSP)]
               ++ substitute asm'
  where
    asm' = concat $ fmap spilled $ avalToMemory asm
    stackOffset = maximum $ [0] ++ do
      line <- asm'
      let v = used line `union` defined line
      [i | Loc (DerefOffset i _) <- Set.toList v]
    substitute ins = do
      i <- ins
      case i of
        RET -> [ADDQ (constant $ 16 + fromIntegral stackOffset) (Loc $ Reg RSP), RET]
        _ -> return i

compile :: Job -> IO ()
compile job = do
  res <- runErrorT $ do
    prog <- parseProgram $ jobSource job :: ErrorT String IO Program
    case elaborate prog of
      Left e -> error (show e)
      Right ast -> do 
        ast' <- liftEIO $ checkAST ast
        if jobOutFormat job == C0
          then writeC0 (jobOut job) ast
          else let asm :: [Instr X86.Expr]
                   asm' = assemble $ allocate $ translate ast' >>= codeGen
                   asm = finalize asm' in
               if jobOutFormat job == Asm
               then do
                 -- lift $ putStrLn $ renderAsm asm'
                 writeAsm (jobOut job) asm
               else do writeAsm asmFile asm
                       let o = if jobOutFormat job == Obj then "-c" else ""
                       gcc o asmFile (jobOut job)
  case res of
    Left msg -> error msg
    Right () -> return ()
  where asmFile = replaceExtension (jobOut job) "s"

gcc :: String -> FilePath -> FilePath -> ErrorT String IO ()
gcc args input output = do
  e <- lift $ system $ "gcc" ++ " " ++ intercalate " " [args, "-m64", input, "l1rt.c", "-o", output]
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
