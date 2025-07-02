module Compile.Types.Assembly where

import Data.Set (Set)
--import qualified Data.Vector as Vec


class Memory m where
  reg :: Int -> m
  constant :: Int -> m

-- Not sure what the best way to store the program as a whole is,
-- so we'll abstract the behavior we need out and decide later.
class Code c where
  -- We will sometimes need to jump backwards. Thus, we need to
  -- have the whole code available at all times.
  -- Since need to be able to find particular spots, we must
  -- have a way of getting the line from an index.
  type Line c
  line :: c i -> Line c -> i
  
  -- We also need to get the next line, if it exists
  next :: Line c -> Maybe (Line c)

-- Consider Enum instead of Code

class Instruction i l where
  used :: i -> Set l
  defined :: i -> Set l

{-
class Assembly a where
  type Line a
  type Instr a
  line :: a -> Line a -> Instr i
  succ :: a -> Line a -> Set (Line a)
  next :: a -> Line a -> Maybe (Line a)
-}
