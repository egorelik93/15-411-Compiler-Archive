{-# LANGUAGE MonadComprehensions, ScopedTypeVariables, InstanceSigs #-}

-- A more memory efficient graph implementation
module Data.Graph.AdjVector where

import Data.Graph.Inductive
import Data.List(find, intercalate, foldl')
import Data.Vector (Vector, (!?), (//))
import qualified Data.Vector as Vec
import qualified Data.Vector.Mutable as MVec
import Data.Foldable (fold)
import Control.Monad (guard)
import Control.Monad.ST (ST)
import Data.Maybe
import Debug.Trace
import Control.Parallel.Strategies
  

data AdjVector a b = AdjVector !(Vector (Maybe a, Adj b, Adj b))
                  deriving Eq

instance (Show a, Show b) => Show (AdjVector a b) where
  show (AdjVector v) = intercalate "\n" $ Vec.toList $ do
    (i, (a, l, _)) <- Vec.indexed v
    case a of
      Just a' -> return $ show i ++ " (" ++ show a' ++ "): " ++ show l
      Nothing -> Vec.empty

instance Graph AdjVector where
  empty = AdjVector Vec.empty
  isEmpty (AdjVector v) = Vec.all (\(l, _, _) -> isNothing l) v

  match :: forall a b . Node -> AdjVector a b -> Decomp AdjVector a b
  match ia (AdjVector v) =
    case v !? ia of
      Nothing -> (Nothing, AdjVector v)
      Just (Nothing, _, _) -> (Nothing, AdjVector v)
      Just (Just a, ls, ts) -> let
        fromA = ls
        toA = ts
        {-  fold $ Vec.imap (\ib (_, vs) ->
                                [(l, ib) | (l, ia') <- vs, ia == ia']
                              ) v-}
        update :: forall s . MVec.MVector s (Maybe a, Adj b, Adj b)
               -> ST s ()
        update v = do
          (_, vs, ts) <- MVec.read v ia
          MVec.write v ia (Nothing, [], [])
          delFromEdges fromA v
          delToEdges toA v
          where
            delNode i = withStrategy (parList rseq) . filter ((/= i) . snd)
            delFromEdges [] v = return () :: ST s ()
            delFromEdges ((_, j) : rest) v = do
              (lJ, fromJ, toJ) <- MVec.read v j
              MVec.write v j (lJ, fromJ, delNode ia toJ)
              delFromEdges rest v
            delToEdges [] v = return ()
            delToEdges ((_, i) : rest) v = do
              (lI, fromI, toI) <- MVec.read v i
              MVec.write v i (lI, delNode ia fromI, toI)
              delToEdges rest v
        in
         (Just (toA, ia, a, fromA), AdjVector $ Vec.modify update v)
  mkGraph [] _ = empty
  mkGraph nodes edges = let
    size = 1 + maximum [i | (i, a) <- nodes]
    init = Vec.generate size $
           \i -> (fmap snd $ find ((== i) . fst) nodes, [], [])
    {-addEdges i l = (l, [(e, j) | (i', j, e) <- edges, i' == i],
                    [(e, j) | (j, i', e) <- edges, i' == i])-}
    addEdges [] v = return ()
    addEdges ((i, j, e) : rest) v = do
      (lI, fromI, toI) <- MVec.read v i
      (lJ, fromJ, toJ) <- MVec.read v j
      MVec.write v i (lI, (e,j) : fromI, toI)
      MVec.write v j (lJ, fromJ, (e,i) : toJ)
      addEdges rest v
    in
     -- AdjVector $ Vec.imap addEdges init
     AdjVector $ Vec.create $ do
       v <- Vec.unsafeThaw init
       addEdges edges v
       return v
  labNodes (AdjVector v) = do
    (i, l) <- Vec.toList $ Vec.imap (\i (l, _, _) -> (i, l)) v
    case l of
      Just l -> return (i, l)
      Nothing -> []

instance DynGraph AdjVector where
  (&) :: forall a b . Context a b -> AdjVector a b -> AdjVector a b
  (to, ia, a, from) & (AdjVector v) =
    case v !? ia of
      Nothing -> mkGraph nodes' edges'
      Just _ -> AdjVector $ Vec.modify update v
    where
      update :: forall s . MVec.MVector s (Maybe a, Adj b, Adj b)
             -> ST s ()
      update v = do
        (_, vs, ts) <- MVec.read v ia
        MVec.write v ia (Just a, vs ++ from, ts ++ to)
        addFromEdges from v
        addToEdges to v
        where
          addFromEdges [] v = return () :: ST s ()
          addFromEdges ((l, j) : rest) v = do
            (lJ, fromJ, toJ) <- MVec.read v j
            MVec.write v j (lJ, fromJ, (l, ia) : toJ)
            addFromEdges rest v
          addToEdges [] v = return ()
          addToEdges ((l, i) : rest) v = do
            (lI, fromI, toI) <- MVec.read v i
            MVec.write v i (lI, (l, ia) : fromI, toI)
            addToEdges rest v
      nodes' = (ia, a) : labNodes (AdjVector v)
      edges' = [(i, ia, l) | (l, i) <- to]
               ++ [(ia, i, l) | (l, i) <- from]
               ++ labEdges (AdjVector v)         
