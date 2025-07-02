{- L1 Compiler
   Author: *[Redacted]
   Modified by: [Redacted]

   Lift IO into Error
-}
module LiftIOE where

import Control.Monad.Error

--TODO make this actually properly catch errors like spoon
liftIOE :: IO a -> ErrorT String IO a
liftIOE = liftIO

liftEIO :: Either String a -> ErrorT String IO a
liftEIO (Left s)  = throwError s
liftEIO (Right x) = return x
