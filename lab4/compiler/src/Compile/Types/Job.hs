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
  }

data OF = C0
        | Asm
        | Obj
        | ELF deriving Eq

defaultJob :: Job
defaultJob = Job {jobOut       = "",
                  jobSource    = "",
                  jobOutFormat = ELF,
                  jobLink = ""}
