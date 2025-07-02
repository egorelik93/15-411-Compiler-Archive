{-# LANGUAGE MonadComprehensions #-}

-- A more memory efficient graph implementation
module Data.Graph.AdjVector where

import Data.Graph.Inductive
import Data.List(find, intercalate)
import Data.Vector (Vector, (!?))
import qualified Data.Vector as Vec
import Data.Foldable (fold)
import Control.Monad (guard)
import Data.Maybe
import Debug.Trace
  

data AdjVector a b = AdjVector (Vector (Maybe a, Adj b))
                  deriving Eq

instance (Show a, Show b) => Show (AdjVector a b) where
  show (AdjVector v) = intercalate "\n" $ Vec.toList $ do
    (i, (a, l)) <- Vec.indexed v
    case a of
      Just a' -> return $ show i ++ " (" ++ show a' ++ "): " ++ show l
      Nothing -> Vec.empty

instance Graph AdjVector where
  empty = AdjVector Vec.empty
  isEmpty (AdjVector v) = Vec.all (\(l, _) -> isNothing l) v
  match ia (AdjVector v) =
    case v !? ia of
      Nothing -> (Nothing, AdjVector v)
      Just (Nothing, _) -> (Nothing, AdjVector v)
      Just (Just a, ls) -> let
        fromA = ls
        toA = fold $ Vec.imap (\ib (_, vs) ->
                                [(l, ib) | (l, ia') <- vs, ia == ia']
                              ) v
        rest = do
          (ib, (b, vs)) <- Vec.indexed v
          if ia == ib
            then return (Nothing, [])
            else return (b, [(l, ic) | (l, ic) <- vs, ic /= ia])
        in
         (Just (toA, ia, a, fromA), AdjVector rest)
  mkGraph [] _ = empty
  mkGraph nodes edges = let
    size = 1 + maximum [i | (i, a) <- nodes]
    init = Vec.generate size $ \i -> fmap snd $ find ((== i) . fst) nodes
    addEdges i l = (l, [(e, j) | (i', j, e) <- edges, i' == i])
    in
     AdjVector $ Vec.imap addEdges init
  labNodes (AdjVector v) = do
    (i, l) <- Vec.toList $ Vec.imap (\i (l, _) -> (i, l)) v
    case l of
      Just l -> return (i, l)
      Nothing -> []

instance DynGraph AdjVector where
  (to, ia, a, from) & (AdjVector v) =
    case v !? ia of
      Nothing -> mkGraph nodes' edges'
      Just _ -> AdjVector $ Vec.imap update v
    where
      nodes' = (ia, a) : labNodes (AdjVector v)
      edges' = [(i, ia, l) | (l, i) <- to]
               ++ [(ia, i, l) | (l, i) <- from]
               ++ labEdges (AdjVector v)
      update i (l, vs) =
        if i == ia
        then (Just a, vs ++ from)
        else (l, vs ++ [(e, ia) | (e, i') <- to, i == i'])
         
