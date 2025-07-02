{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Compile.SymbolGen where

import Control.Monad.Trans.State
import Data.Heap (MinHeap)
import qualified Data.Heap as Heap


newtype SymbolGen a = SymbolGen (State (Int, MinHeap Int) a)
                deriving (Functor, Monad)

allocate :: SymbolGen a -> a
allocate (SymbolGen s) = evalState s (0, Heap.empty)

newIndex :: SymbolGen Int
newIndex = SymbolGen $ do
  (n, heap) <- get
  case Heap.view heap of
    Nothing -> do
      put (n + 1, heap)
      return n
    Just (i, heap') -> do
      put (n, heap')
      return i

freeIndex :: Int -> SymbolGen ()
freeIndex i = SymbolGen $ do
  (n, heap) <- get
  if i >= n
    then return ()
    else put (n, Heap.insert i heap)
