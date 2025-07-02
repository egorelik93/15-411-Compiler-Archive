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
    init = Map.fromList $
           [((n, AReg i), i) | (n, AReg i) <- vars] ++
           [((n, AArg i), arg' i) | (n, AArg i) <- vars, 1 <= i, i <= 6]
    arg' i = case arg i of
      Reg r -> fromEnum r
      _ -> i
      

interferenceGraph :: [Instr AVal] -> InterferenceGraph ALoc
interferenceGraph ins = fst $ mkMapGraph (Set.toList vars) interference
{-
                        foldr (insMapEdge nodeMap)
                        emptyGraph 
                        interference -}
  where
    ins' = Vec.fromList ins
    vars = Vec.foldl' (\v l -> v `union` getALoc (used l `union` defined l))
           Set.empty
           ins'
    {-vars = Vec.foldl (\v l -> v `union` getALoc (defined l))
           Set.empty
           ins'-}
           {-
    (emptyGraph, nodeMap, _) = Set.foldr (\a (g, m, _) -> insMapNode m a g)
                               (Graph.empty, new, undefined)
                               vars
-}
    info = liveness ins'
    mkLabel i (Label s) m = Map.insert s i m
    mkLabel _ _ m = m
    labelMap = Vec.ifoldr' mkLabel Map.empty ins'
    getALoc' (ALoc _ (AAddr v)) s = getALoc' v s
    getALoc' (ALoc _ (AIndex _ x i _)) s =
      Set.union (getALoc' x s) (getALoc' i s)
    getALoc' (ALoc _ (AOffset _ x)) s = getALoc' x s
    getALoc' (ALoc _ x) s = Set.insert x s
    getALoc' _ s = s
    getALoc = Set.foldr' getALoc' Set.empty
    lineInfo i l = (,) l $ do
      s <- Set.toList $ successors l
      case s of
        NextLine -> case (Vec.!?) info (i + 1) of
          Just l -> return $ getALoc l
          Nothing -> []
        LineLabel lbl -> return $ getALoc $ (Vec.!) info (labelMap ! lbl)
    instrWithLive = Vec.imap lineInfo ins'
    interference = do
      (l, succsLive) <- Vec.toList instrWithLive
      v <- succsLive
      d <- Set.toList $ getALoc $ defined l
      ALoc _ var <- Set.toList $ interfere l $ Set.map (ALoc Q) v 
      -- if var /= d then return (var, d, ())
      --   else []
      return (var, d, ())
    
    
avalToMemory :: [Instr AVal] -> (Map.Map ALoc Loc,
                                 [Expr], [Instr Expr])
avalToMemory p = (alloc', needToSave, fmap (fmap convert) p)
  where
    maxArgs = case [length args | CALL _ args <- p] of
      [] -> 0
      l -> maximum l
    graph = undir $ interferenceGraph p
    alloc = registerAllocate graph
    needToSave = nub [loc Q r | r <- Map.elems alloc',
                      calleeSave r]
    offset = toInteger $ 8 * maxArgs
    reg' i =
      case reg i of
        DerefOffset o r ->
          DerefOffset (o + offset) r
        r -> r
    alloc' = Map.map reg' alloc
    convert (ALoc s (ATemp i)) = loc s $ alloc' ! ATemp i
    convert (ALoc s (AReg i)) = loc s $ reg i
    convert (AImm i) = constant i
    convert (ALoc s (AArg i)) = loc s $ arg i
    convert (ALoc s (AAddr v)) = loc s $ Deref $ convert v
    convert (ALoc _ (AIndex o x i s)) = mem o (convert x) (Just $ convert i) s
    convert (ALoc s (AOffset o x)) = mem o (convert x) Nothing s
