{- L1 Compiler
   Author: *[Redacted]
   Modified by: [Redacted]

   the entry point to the compiler
-}
import Compile
import Args
import System.Environment
import System.IO
import System.Exit

getDefaults "c0c" = defaultJob
getDefaults "l1c" = defaultJob {jobOutFormat = Asm}
getDefaults _ = defaultJob

main :: IO ()
main = do
  prog <- getEnv "COMPILER"
  args <- getArgs
  case parseArgs (getDefaults prog) args of
    Left  err -> do hPrint stderr err
                    hPutStr stderr (usage prog)
                    exitFailure
    Right job -> compile job
  exitSuccess
