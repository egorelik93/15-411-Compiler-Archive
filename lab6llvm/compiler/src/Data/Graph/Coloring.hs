module Data.Graph.Coloring where

import Control.Monad.Trans.State
import Data.Graph.Inductive
import Data.IntSet (IntSet, member, union)
import qualified Data.IntSet as Set
import Data.Map ((!))
import qualified Data.Map as Map
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.List(find, (\\), nub, sort)
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet


elimOrder :: Graph gr => gr a b -> [LNode a]
elimOrder g = evalState update init
  where
    verts = labNodes g
    init = IntMap.fromList [(vi, (vl, 0)) | (vi, vl) <- verts]
    updateIfMember nb xi (xl, wt) | xi `member` nb = (xl, wt - 1)
                                  | otherwise = (xl, wt)

    update = do
      wts <- get
      if IntMap.null wts
        then return []
        else do
          let minWt xi (xl, xwt) (yi, yl, ywt)
                | xwt <= ywt = (xi, xl, xwt)
                | otherwise = (yi, yl, ywt)
              (vi, vl, _) = IntMap.foldrWithKey minWt (0, undefined, 0) wts
              wts' = IntMap.delete vi wts
              nbs = Set.fromList $ suc g vi
          put $ IntMap.mapWithKey (updateIfMember nbs) wts'
          rest <- update
          return $ (vi, vl) : rest

lowestNotin :: [Int] -> Int
lowestNotin l = let
  set = IntSet.fromList l
  in
   case find (\x -> IntSet.notMember x set) [0 ..] of
     Just i -> i
     Nothing -> IntSet.size set

  {-
  case find (\(x,y) -> x /= y) $ zip (nub $ sort l) [0 ..] of
        Just (_, i) -> i
        Nothing -> length l-}

color :: (Graph gr, Ord a) => gr a b -> [LNode a] -> Map.Map (LNode a) Int -> Map.Map (LNode a) Int
color g l m = execState (update $ l \\ Map.keys m ) m
  where
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
