module Compile.RegisterAllocator where

import Control.Monad.Trans.State
import Data.Graph.Inductive as Graph hiding (Gr)
import Data.Set (Set, member, union)
import qualified Data.Set as Set
import Data.Graph.Inductive.Internal.Heap
import Data.Map ((!))
import qualified Data.Map as Map
import Data.List(find, (\\), nub, sort)
import Data.Vector (Vector)
import qualified Data.Vector as Vec
import Data.Graph.AdjVector
import Data.Graph.Coloring
import Debug.Trace

import Compile.Types.AbstractAssembly(ALoc(..), AVal(..))
import Compile.Types.X86_64
import Compile.Types.Assembly
import Compile.Analysis


type InterferenceGraph a = AdjVector a ()


registerAllocate :: InterferenceGraph ALoc -> Map.Map ALoc Int
registerAllocate g = optimalColoring g init
  where
    vars = labNodes g
    init = Map.fromList [((n, AReg i), i) | (n, AReg i) <- vars]

interferenceGraph :: [Instr AVal] -> InterferenceGraph ALoc
interferenceGraph ins = fst $ mkMapGraph (Set.toList vars) interference
{-
                        foldr (insMapEdge nodeMap)
                        emptyGraph 
                        interference -}
  where
    ins' = Vec.fromList ins
    vars = Vec.foldl (\v l -> v `union` getALoc (used l `union` defined l))
           Set.empty
           ins'
           {-
    (emptyGraph, nodeMap, _) = Set.foldr (\a (g, m, _) -> insMapNode m a g)
                               (Graph.empty, new, undefined)
                               vars
-}
    info = liveness ins'
    mkLabel i (Label s) m = Map.insert s i m
    mkLabel _ _ m = m
    labelMap = Vec.ifoldr mkLabel Map.empty ins'
    getALoc' (ALoc x) s = Set.insert x s
    getALoc' _ s = s
    getALoc = Set.foldr getALoc' Set.empty
    lineInfo i l = (,) l $ do
      s <- Set.toList $ successors l
      case s of
        NextLine -> return $ getALoc $ (Vec.!) info (i + 1)
        LineLabel lbl -> return $ getALoc $ (Vec.!) info (labelMap ! lbl)
    instrWithLive = Vec.imap lineInfo ins'
    interference = do
      (l, succsLive) <- Vec.toList instrWithLive
      v <- succsLive
      d <- [x | ALoc x <- Set.toList $ defined l]
      ALoc var <- Set.toList $ interfere l $ Set.map ALoc v 
      -- if var /= d then return (var, d, ())
      --   else []
      return (var, d, ())
    
    
avalToMemory :: Memory m => [Instr AVal] -> [Instr m]
avalToMemory p = fmap (fmap convert) p
  where
    graph = undir $ interferenceGraph p
    alloc = registerAllocate graph
    convert (ALoc l) = reg $ alloc ! l
    convert (AImm i) = constant i
