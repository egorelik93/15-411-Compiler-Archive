{- L1 Compiler
   Author: *[Redacted]
   Modified by: [Redacted]

   Defines a compiler phase or job
-}
module Compile.Types.Job where

data Job = Job
  { jobOut       :: FilePath
  , jobSource    :: FilePath
  , jobOutFormat :: OF
  , jobLink      :: FilePath
  , jobSafe    :: Bool
  , jobOpt     :: Opt
  }

data OF = C0
        | Asm
        | Obj
        | ELF deriving Eq

data Opt = O0
         | O1
         | O2
         deriving (Eq, Show)

defaultJob :: Job
defaultJob = Job {jobOut       = "",
                  jobSource    = "",
                  jobOutFormat = ELF,
                  jobLink = "",
                  jobSafe = True,
                  jobOpt = O2}
