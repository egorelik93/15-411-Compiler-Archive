module Data.Graph.Coloring where

import Control.Monad.Trans.State
import Data.Graph.Inductive
import Data.Set (Set, member, union)
import qualified Data.Set as Set
import Data.Graph.Inductive.Internal.Heap
import Data.Map ((!))
import qualified Data.Map as Map
import Data.List(find, (\\), nub, sort)


elimOrder :: Graph gr => gr a b -> [LNode a]
elimOrder g = evalState update init
  where
    verts = labNodes g
    init = map ((,) 0) verts
    updateIfMember nb (wt, (xi, xl)) | xi `member` nb = (wt - 1, (xi, xl))
                                     | otherwise = (wt, (xi, xl))

    update = do
      wts <- get
      case wts of
        [] -> return []
        _ -> do
          let heap = build wts
              (_, (vi, vl)) = findMin heap
              wts' = toList $ deleteMin heap
              nbs = Set.fromList $ suc g vi
          put $ map (updateIfMember nbs) wts'
          rest <- update
          return $ (vi, vl) : rest

color :: (Graph gr, Ord a) => gr a b -> [LNode a] -> Map.Map (LNode a) Int -> Map.Map (LNode a) Int
color g l m = execState (update $ l \\ Map.keys m ) m
  where
    lowestNotin l =
      case find (\(x,y) -> x /= y) $ zip (nub $ sort l) [0 ..] of
        Just (_, i) -> i
        Nothing -> length l
    update [] = return ()
    update ((xi, xl) : xs) = do
      m' <- get :: State (Map.Map (LNode a) Int) (Map.Map (LNode a) Int)
      let nbs = Set.fromList $ suc g xi
          colored = Map.elems $
                    Map.filterWithKey (\(i, _) _ -> i `member` nbs) m'
          next = lowestNotin colored
      put $ Map.insert (xi, xl) next m'
      update xs

optimalColoring :: (Graph gr, Ord a) => gr a b -> Map.Map (LNode a) Int -> Map.Map a Int
optimalColoring g = Map.mapKeys snd . color g (elimOrder g)
