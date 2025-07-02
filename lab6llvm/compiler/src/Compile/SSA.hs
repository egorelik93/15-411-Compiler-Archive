module Compile.SSA where

import Prelude hiding (mapM, sequence, msum)
import Control.Monad.Trans.State
import Data.Map (Map, (!))
import Control.Monad.Trans
import qualified Data.Map as Map
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad.Free.Class
import qualified Control.Monad.Free as FM
import qualified Control.MonadOr.Free as FMP
import qualified Control.Monad.Trans.Free as FMF
import Control.Comonad.Trans.Env
import Data.Traversable
import Data.Foldable (msum)
import Text.Parsec.Pos (SourcePos)
import Data.Monoid
import Data.Heap (MinHeap)
import qualified Data.Heap as Heap
import Data.List (find, reverse)
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Text.PrettyPrint.HughesPJ
import Debug.Trace

import Compile.Types
import Compile.Types.Assembly
import Compile.SymbolGen
import Compile.TypeChecker (subst, subst')
import Compile.Translation (true, false)
import Compile.Types.X86_64



usedInALocs :: Size -> ALoc -> Set (Size, ALoc)
usedInALocs _ (AAddr v) = usedALocs v
usedInALocs _ (AIndex _ v1 v2 _) = Set.union (usedALocs v1) (usedALocs v2)
usedInALocs _ (AOffset _ v) = usedALocs v
usedInALocs s a = Set.singleton (s, a)

usedALocs :: AVal -> Set (Size, ALoc)
usedALocs (AImm _) = Set.empty
usedALocs (ALoc s v) = usedInALocs s v


usedInTerm :: Term AVal -> Set (Size, ALoc)
usedInTerm (BinOp _ e1 e2) = Set.union (usedALocs e1) (usedALocs e2)
usedInTerm (UnOp _ e) = usedALocs e
usedInTerm (Call _ es) = Set.unions $ map usedALocs es

usedInExit :: Exit Int (Term AVal) -> Set (Size, ALoc)
usedInExit (IfElseGoto e _ _) = usedInTerm e
usedInExit (Goto _) = Set.empty
usedInExit (Return e) = usedInTerm e

usedInDefine :: Define (Size, ALoc) (Term AVal) -> Set (Size, ALoc)
usedInDefine (Define (s, v) e) =
  if onHeap (ALoc s v)
  then Set.union (usedInALocs s v) (usedInTerm e)
  else usedInTerm e

liveInBlock :: Set (Size, ALoc)
            -> ([Define (Size, ALoc) (Term AVal)], Exit Int (Term AVal))
            -> Set (Size, ALoc)
liveInBlock live ([], exit) = Set.union (usedInExit exit) live
liveInBlock live (d@(Define (s, asn) e) : rest, exit) =
  Set.union (usedInDefine d) (Set.filter ((/= asn) . snd) $
                              liveInBlock live (rest, exit))

{-
initLiveBlocks :: Blocks (Size, ALoc) (Term AVal)
             -> (Int, IntMap (Set ALoc, [Define asn exp], Exit Int exp))
initLiveBlocks (i, blks) =
  (i, IntMap.map (\(defs, exit) ->
                   (liveInBlock (defs, exit), defs, exit))
      blks)-}

{-
definedInBlock :: [Define (Size, ALoc) (Term AVal)] -> Set ALoc
definedInBlock [] = Set.empty
definedInBlock (Define (_, asn) e : rest) =
  Set.filter (Set.notMember $ usedInTerm e)-}

liveBlocks' :: Blocks (Size, ALoc) (Term AVal) -> IntMap (Set (Size, ALoc))
            -> State (IntMap (Set (Size, ALoc)))
               (Set (Size, ALoc))
liveBlocks' (i, blks) orig = do
  liveness <- get
  case IntMap.lookup i liveness of
    Just live -> return live
    Nothing -> do
      let (defs, exit) =
            case IntMap.lookup i blks of
              Just e -> e
              Nothing -> error $ "Can't find block of label .l" ++ show i
          old = case IntMap.lookup i orig of
              Just e -> e
              Nothing -> Set.empty
          succs (Return _) = []
          succs (Goto lbl) = [lbl]
          succs (IfElseGoto _ lbl1 lbl2) = [lbl1, lbl2]
          -- defined = definedInBlock defs
      let tempLive = liveInBlock old (defs, exit)
      put (IntMap.insert i tempLive liveness)
      live <- mapM (\i -> liveBlocks' (i, blks) orig) (succs exit)
      let newLive = liveInBlock (Set.unions live) (defs, exit)
      liveness' <- get
      put (IntMap.insert i newLive liveness')
      return newLive
    
liveBlocks :: (Int, IntMap ([Define (Size, ALoc) (Term AVal)],
                            Exit Int (Term AVal)))
           -> (Int, IntMap ([(Size, ALoc)], [Define (Size, ALoc) (Term AVal)],
                            Exit Int (Term AVal)))
liveBlocks (i, blks) =
  let init = execState (liveBlocks' (i, blks) IntMap.empty) IntMap.empty
      propogate live =
        let result = execState (liveBlocks' (i, blks) live) IntMap.empty
        in
         if live == result
         then result
         else propogate result
      liveMap = propogate init
  in (i, IntMap.mapWithKey (\k (defs, exit) -> 
                             (case IntMap.lookup k liveMap of
                                 Just s -> Set.toList s
                                 Nothing -> [],
                              defs, exit)) blks)

usedInBlocks :: Blocks (Size, ALoc) (Term AVal)
             -> (Int, IntMap (Set (Size, ALoc),
                              [Define (Size, ALoc) (Term AVal)],
                              Exit Int (Term AVal)))
usedInBlocks (i, blks) =
  (i, IntMap.map
      (\(defs, exit) ->
        (Set.union (Set.unions (map usedInDefine defs))
         (usedInExit exit)
         , defs, exit))
      blks)
                                      
                

toSSA :: Blocks (Size, ALoc) (Term AVal) -> SymbolGen (SSA (Size, ALoc) (Term AVal))
toSSA blks = let
  (i, blks') = liveBlocks blks
  getLblLive lbl = case IntMap.lookup lbl blks' of
    Just (vs, _, _) -> vs
    Nothing -> []
  parameterize (Return e) = Return e
  parameterize (Goto lbl) = Goto (lbl, getLblLive lbl)
  parameterize (IfElseGoto e lbl1 lbl2) = IfElseGoto e
                                          (lbl1, getLblLive lbl1)
                                          (lbl2, getLblLive lbl2)
  parameterizedBlks = IntMap.map
                      (\(l, defs, exit) -> (l, defs, parameterize exit))
                      blks'
  getGen (s, v@(ATemp _)) = do
    genMap <- get
    case Map.lookup v genMap of
      Just i -> return (s, i)
      Nothing -> return (s, v)
  getGen v = return v
      
  newGen v@(ATemp _) = do
    genMap <- get
    i <- lift newIndex
    let genMap' = Map.insert v (ATemp i) genMap
    put genMap'
    return $ ATemp i
  newGen v = return v

  newLive (s, t) = do
    t' <- newGen t
    return (s, t')

  substGen (ALoc s t@(ATemp _)) = do
    (_, g) <- getGen (s, t)
    return $ ALoc s g
  substGen (ALoc s (AAddr v)) = do
    g <- substGen v
    return $ ALoc s (AAddr g)
  substGen (ALoc s (AIndex o x e s')) = do
    x' <- substGen x
    e' <- substGen e
    return $ ALoc s (AIndex o x' e' s')
  substGen (ALoc s (AOffset i v)) = do
    v' <- substGen v
    return $ ALoc s (AOffset i v')
  substGen v = return v
  
  genDefine (Define (s, t@(ATemp _)) e) = do
    e' <- mapM substGen e
    t' <- newGen t
    return $ Define (s, t') e' 
  genDefine (Define (s, AAddr v) e) = do
    e' <- mapM substGen e
    v' <- substGen v
    return $ Define (s, AAddr v') e'
  genDefine (Define (s, AIndex o x i s') e) = do
    e' <- mapM substGen e
    x' <- substGen x
    i' <- substGen i
    return $ Define (s, AIndex o x' i' s') e'
  genDefine (Define (s, AOffset i v) e) = do
    e' <- mapM substGen e
    v' <- substGen v
    return $ Define (s, AOffset i v') e'
  genDefine (Define t e) = do
    e' <- mapM substGen e
    return $ Define t e'

  genExit (Goto (lbl, params)) = do
    params' <- mapM getGen params
    return $ Goto (lbl, params')
  genExit (Return e) = do
    e' <- mapM substGen e
    return $ Return e'
  genExit (IfElseGoto e (l1, params1) (l2, params2)) = do
    e' <- mapM substGen e
    params1' <- mapM getGen params1
    params2' <- mapM getGen params2
    return $ IfElseGoto e' (l1, params1') (l2, params2')
    
  generation (live, defs, exit) = do
    live' <- mapM newLive live
    defs' <- mapM genDefine defs
    exit' <- genExit exit
    return (live', defs', exit')
    
  ssa = mapM generation parameterizedBlks
    
  in do
   ssa' <- evalStateT ssa Map.empty
   return ((i, getLblLive i), ssa')



toSSAPhi :: SSA (Size, ALoc) (Term AVal) -> SSAPhi (Size, ALoc) (Term AVal)
toSSAPhi ((i, args), blks) = let
  getLblLive lbl = case IntMap.lookup lbl blks of
    Just (vs, _, _) -> vs
    Nothing -> []

  stripExit exit = case exit of
    Return e -> Return e
    Goto (lbl, _) -> Goto lbl
    IfElseGoto e (lbl1, _) (lbl2, _) -> IfElseGoto e lbl1 lbl2
  
  addToLabel curr (lbl, args) = do
    prog <- get
    let live = getLblLive lbl
    case IntMap.lookup lbl prog of
      Just (phi, defs, exit) -> do
        let liveWArgs = zip live args
            update (param, arg) from =
              Map.insertWith (++) param [(arg, curr)] from
            phi' = foldr update phi liveWArgs
            prog' = IntMap.insert lbl (phi', defs, exit) prog
        put prog'
      Nothing ->
        case IntMap.lookup lbl blks of
          Nothing -> error $ "Couldn't find label " ++ show lbl
          Just (live, defs, exit) -> do
            let liveWArgs = zip live args
                update (param, arg) from =
                  Map.insertWith (++) param [(arg, curr)] from
                phi = foldr update Map.empty liveWArgs
                prog' = IntMap.insert lbl (phi, defs, stripExit exit) prog
            put prog'
            toPhiBlk lbl exit
      
  toPhiBlk i exit = do
    prog <- get
    let labels = case exit of
          Return _ -> []
          Goto lbl -> [lbl]
          IfElseGoto _ lbl1 lbl2 -> [lbl1, lbl2]
    mapM_ (addToLabel i) labels

  start = case IntMap.lookup i blks of
    Nothing -> error $ "Couldn't find label " ++ show i
    Just (live, defs, exit) -> do
      prog <- get
      let liveWArgs = zip live args
          define (param, (s, arg)) = Define param $ UnOp Nop (ALoc s arg)
          defs' = map define liveWArgs ++ defs
          exit' = stripExit exit
          prog' = IntMap.insert i (Map.empty, defs', exit') prog
      put prog'
      toPhiBlk i exit
  in
   (i, execState start IntMap.empty)
    
    

deSSA :: SSA (Size, ALoc) (Term AVal) -> SymbolGen (Blocks (Size, ALoc) (Term AVal))
deSSA ((i, args), blks) = let
  getLblLive lbl = case IntMap.lookup lbl blks of
    Just (vs, _, _) -> vs
    Nothing -> []

  deParameterize i (live, defs, exit) rest' = do
    rest <- rest'
    case exit of
      Return e -> return $ IntMap.union rest
                  (IntMap.singleton i (defs, Return e))
      Goto (lbl, args) -> let
        params = getLblLive lbl
        paramsWArgs = zip params args
        getParams = map (\(p, (s, a)) ->
                          Define p (UnOp Nop (ALoc s a))) paramsWArgs
        in
         return $ IntMap.union rest
         (IntMap.singleton i (defs ++ getParams, Goto lbl))
      IfElseGoto e (lbl1, args1) (lbl2, args2) -> let
        params1 = getLblLive lbl1
        paramsWArgs1 = zip params1 args1
        getParams1 = map (\(p, (s, a)) ->
                           Define p (UnOp Nop (ALoc s a))) paramsWArgs1
        params2 = getLblLive lbl2
        paramsWArgs2 = zip params2 args2
        getParams2 = map (\(p, (s, a)) ->
                           Define p (UnOp Nop (ALoc s a))) paramsWArgs2
        in do
          l1 <- newIndex
          l2 <- newIndex
          let (blockl1, lbl1') = case getParams1 of
                [] -> (IntMap.empty, lbl1)
                _ -> (IntMap.singleton l1 (getParams1, Goto lbl1), l1)
              (blockl2, lbl2') = case getParams2 of
                [] -> (IntMap.empty, lbl2)
                _ -> (IntMap.singleton l2 (getParams2, Goto lbl2), l2)
          return $ IntMap.unions
            [rest,
             blockl1, blockl2,
             IntMap.singleton i (defs, IfElseGoto e lbl1' lbl2')]
  in do
    result <- IntMap.foldrWithKey deParameterize (return IntMap.empty) blks
    let params = getLblLive i
        paramsWArgs = zip params args
        getParams = map (\(p, (s, a)) ->
                          Define p (UnOp Nop (ALoc s a))) paramsWArgs
        result' = IntMap.update
                  (\(defs, exit) -> Just (getParams ++ defs, exit))
                  i result
    return (i, result')      
          
      
