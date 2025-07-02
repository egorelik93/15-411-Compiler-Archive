module Compile.Types.Assembly where

import Data.Set (Set)
--import qualified Data.Vector as Vec


class Location (MemoryLoc m) => Memory m where
  type MemoryLoc m
  constant :: Int -> m
  loc :: Size -> MemoryLoc m -> m
  mem :: Int -> m -> Maybe m -> Size -> m
  onHeap :: m -> Bool

class Location l where
  reg :: Int -> l
  arg :: Int -> l

data Size = B
          | S
          | L
          | Q
          | Aggregate [Size]
          deriving (Eq, Show, Ord)

bytes :: Size -> Int
bytes B = 1
bytes S = 2
bytes L = 4
bytes Q = 8
bytes (Aggregate ss) =
  let total = sum $ map bytes ss in
  case total `mod` 8 of
    0 -> total
    r -> total + (8 - r)

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

data LineID lbl = LineLabel lbl
                | NextLine
                deriving (Eq, Show, Ord)

class Instruction i where
  type Val i
  type Label i
  used :: i -> Set (Val i)
  defined :: i -> Set (Val i)
  successors :: i -> Set (Label i)

{-
class Assembly a where
  type AssInstr 
  label :: Label i -> i -> i
-}

{-
class Assembly a where
  type Line a
  type Instr a
  line :: a -> Line a -> Instr i
  succ :: a -> Line a -> Set (Line a)
  next :: a -> Line a -> Maybe (Line a)
-}
