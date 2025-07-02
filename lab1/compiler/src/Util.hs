{- L1 Compiler
   Author: *[Redacted]
   Modified by: [Redacted]

   Some utility functions; these are generally defined in newer versions of GHC, but not the version
   provided on the Andrew machines.
-}
module Util where

swap :: (a, b) -> (b, a)
swap = uncurry $ flip (,)

void :: Functor f => f a -> f ()
void = fmap (const ())
