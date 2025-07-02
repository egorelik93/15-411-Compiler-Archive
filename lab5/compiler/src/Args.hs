{- L1 Compiler
   Author: *[Redacted]
   Modified by: [Redacted]

   Argument and option parsing
-}
module Args (parseArgs, JobParseError(..), usage) where

import Compile.Types.Job
import System.Console.GetOpt
import Util
import Data.Maybe
import System.FilePath

data JobParseError = NoSources
                   | TooManySources
                   | GetOptError [String] deriving Show

usage :: String -> String
usage p = usageInfo p argTable

parseArgs :: Job -> [String] -> Either JobParseError Job
parseArgs initialJob args = let
  (transforms, sources, errors) = getOpt Permute argTable args
  in case errors of
       [] -> case sources of
               []        -> Left NoSources
               _ : _ : _ -> Left TooManySources
               [source]  -> Right $ ensureOut $ (foldr ($) initialJob transforms) {jobSource = source}
       _  -> Left $ GetOptError errors

argTable :: [OptDescr (Job -> Job)]
argTable = [
  Option ['o'] ["out"] (ReqArg setOut "out.S") "Redirects output of the compiler to a particular target file. Will attempt to autodetect output type. - represents stdout.",
  Option ['S'] ["asm"] (NoArg (setOF Asm)) "Sets the output target to be assembly type.",
  Option ['c'] ["obj"] (NoArg (setOF Obj)) "Sets the output target to be an elf intermediate object.",
  Option ['E'] ["pretty"] (NoArg (setOF C0)) "Sets the output type to be C0 (act as a pretty printer).",
  Option ['e'] ["elf"] (NoArg (setOF ELF)) "Produces a full fledged ELF executable, ready to run.",
  Option ['l'] [] (ReqArg setLink "15411.h0") "Links a header file.",
  Option [] ["unsafe"] (NoArg setUnsafe) "Generates unchecked code.",
  Option [] ["safe"] (NoArg id) "Generates checked code (default).",
  Option ['O'] [] (ReqArg setOpt "[0-2]") "Sets the optimization level"
  ]

setOF :: OF -> Job -> Job
setOF outFormat j = j {jobOutFormat = outFormat}

extTable :: [(String, OF)]
extTable = [(".s", Asm), (".o", Obj), (".c", C0), ("", ELF)]

revExtTable :: [(OF, String)]
revExtTable = map swap extTable

setOut :: FilePath -> Job -> Job
setOut out j = let
  base = j {jobOut = out}
  in case lookup (takeExtension out) extTable of
       Just f  -> setOF f base
       Nothing -> base

setLink :: FilePath -> Job -> Job
setLink link j = j {jobLink = link}

setOpt :: String -> Job -> Job
setOpt "0" j = j {jobOpt = O0}
setOpt "1" j = j {jobOpt = O1}
setOpt "2" j = j {jobOpt = O2}
setOpt _ _ = error "Error: Not a valid optimization level. Choose a level 0 - 2."

setUnsafe :: Job -> Job
setUnsafe j = j {jobSafe = False}

ensureOut :: Job -> Job
ensureOut j = case jobOut j of
  "" -> j {jobOut = replaceExtension (jobSource j) $ objExt (jobOutFormat j)}
  _  -> j
  where objExt obj = fromJust $ lookup obj revExtTable
