module Compile.Optimization where

import Prelude hiding (mapM, sequence, msum)
import Control.Monad.Trans.State
import Data.Map (Map)
import Control.Monad.Trans
import qualified Data.Map as Map
import Data.IntMap (IntMap, (!))
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
import Compile.SSA


boolToVal :: Bool -> Int
boolToVal True = true
boolToVal False = false

substAVal :: AVal -> AVal -> AVal -> AVal
substAVal v e t | v == t = e
                | otherwise = t

propBlock :: SSA (Size, ALoc) (Term AVal)
             -> State (Map AVal AVal, SSA (Size, ALoc) (Term AVal)) ()
propBlock (i, ssa) = do
  (_, (_, currentSSA)) <- get
  case IntMap.lookup (fst i) currentSSA of
    Just _ -> return ()
    Nothing -> do
      let addDef (Define (s, ATemp i) (UnOp Nop e))
            | not (onHeap e) = do
            (optMap, ssa) <- get
            put (Map.insert (ALoc s (ATemp i)) e optMap, ssa)
          addDef (Define (s, ATemp i) (UnOp Neg (AImm e))) = do
            (optMap, ssa) <- get
            put (Map.insert (ALoc s (ATemp i)) (AImm $ -e) optMap, ssa)
          addDef (Define (s, ATemp i) (BinOp Add (AImm a) (AImm b))) = do
            (optMap, ssa) <- get
            put (Map.insert (ALoc s (ATemp i)) (AImm $ a + b) optMap, ssa)
          addDef (Define (s, ATemp i) (BinOp Sub (AImm a) (AImm b))) = do
            (optMap, ssa) <- get
            put (Map.insert (ALoc s (ATemp i)) (AImm $ a - b) optMap, ssa)
          addDef (Define (s, ATemp i) (BinOp Mul (AImm a) (AImm b))) = do
            (optMap, ssa) <- get
            put (Map.insert (ALoc s (ATemp i)) (AImm $ a * b) optMap, ssa)
          addDef (Define (s, ATemp i) (BinOp Eq (AImm a) (AImm b))) = do
            (optMap, ssa) <- get
            put (Map.insert (ALoc s (ATemp i))
                 (AImm $ boolToVal $ a == b) optMap, ssa)
          addDef (Define (s, ATemp i) (BinOp NEq (AImm a) (AImm b))) = do
            (optMap, ssa) <- get
            put (Map.insert (ALoc s (ATemp i))
                 (AImm $ boolToVal $ a /= b) optMap, ssa)
          addDef (Define (s, ATemp i) (BinOp Lt (AImm a) (AImm b))) = do
            (optMap, ssa) <- get
            put (Map.insert (ALoc s (ATemp i))
                 (AImm $ boolToVal $ a < b) optMap, ssa)
          addDef (Define (s, ATemp i) (BinOp LtE (AImm a) (AImm b))) = do
            (optMap, ssa) <- get
            put (Map.insert (ALoc s (ATemp i))
                 (AImm $ boolToVal $ a <= b) optMap, ssa)
          addDef (Define (s, ATemp i) (BinOp Gt (AImm a) (AImm b))) = do
            (optMap, ssa) <- get
            put (Map.insert (ALoc s (ATemp i))
                 (AImm $ boolToVal $ a > b) optMap, ssa)
          addDef (Define (s, ATemp i) (BinOp GtE (AImm a) (AImm b))) = do
            (optMap, ssa) <- get
            put (Map.insert (ALoc s (ATemp i))
                 (AImm $ boolToVal $ a >= b) optMap, ssa)
          addDef _ = return ()
          {-trySubstAVal (ALoc s (AAddr v)) = do
            result <- trySubstAVal v
            case result of
              ALoc _ _ -> return $ ALoc s (AAddr result)
              _ -> return v
          trySubstAVal (ALoc s (AOffset o v)) = do
            result <- trySubstAVal v
            case result of
              ALoc _ _ -> return $ ALoc s (AOffset o result)
              _ -> return v-}
          trySubstAVal v = do
            (optMap, _) <- get
            case Map.lookup v optMap of
              Nothing -> return v
              Just e -> return e
          trySubst (Define v e) = do
            e' <- mapM trySubstAVal e
            return $ Define v e'
          tryExit (Return e) = do
            e' <- mapM trySubstAVal e
            return $ Return e'
          tryExit (Goto (lbl, params)) = return (Goto (lbl, params))
          tryExit (IfElseGoto e (lbl1, params1) (lbl2, params2)) = do
            e' <- mapM trySubstAVal e
            case e' of
              BinOp op (AImm a) (AImm b)
                | op `elem` [Eq, NEq, Lt, LtE, Gt, GtE] ->
                  let evalOp = case op of
                        Eq -> (==)
                        NEq -> (/=)
                        Lt -> (<)
                        LtE -> (<=)
                        Gt -> (>)
                        GtE -> (>=)
                  in
                   if evalOp a b then return $ Goto (lbl1, params1)
                   else return $ Goto (lbl2, params2)
              UnOp Nop (AImm i) ->
                if i == true
                then return $ Goto (lbl1, params1)
                else return $ Goto (lbl2, params2)
              UnOp Not (AImm i) ->
                if i == false
                then return $ Goto (lbl1, params1)
                else return $ Goto (lbl2, params2)
              _ -> return $ IfElseGoto e' (lbl1, params1) (lbl2, params2)
          (live, defs, exit) = ssa ! (fst i)
          eval defs = do
            mapM_ addDef defs
            defs' <- mapM trySubst defs
            if defs == defs' then return defs'
              else eval defs'
      defs' <- eval defs
      exit' <- tryExit exit
      (optMap, (k, currentSSA)) <- get
      put (optMap, (k, IntMap.insert (fst i) (live, defs', exit') currentSSA))
      case exit of
        Return _ -> return ()
        Goto lbl -> propBlock (lbl, ssa)
        IfElseGoto _ lbl1 lbl2 -> do
          propBlock (lbl1, ssa)
          propBlock (lbl2, ssa)


constCopyPropagate :: SSA (Size, ALoc) (Term AVal)
                   -> SSA (Size, ALoc) (Term AVal)
constCopyPropagate (i, ssa) = snd $ execState (propBlock (i,ssa))
                              (Map.empty, (i, IntMap.empty))



type NeedInfo = IntMap (Set (Size, ALoc), [(Size, ALoc)],
                           [(Define (Size, ALoc) (Term AVal),
                             Set (Size, ALoc))],
                           (Exit (Int, [(Size, ALoc)]) (Term AVal),
                            Set (Size, ALoc)))

necDefine :: Define (Size, ALoc) (Term AVal) -> Set (Size, ALoc)
necDefine d@(Define (s, v) (UnOp Nop e))
  | onHeap (ALoc s v) = usedInDefine d
  | onHeap e = usedALocs e
necDefine d@(Define (s, v) e)
  | onHeap (ALoc s v) = usedInDefine d
necDefine (Define x t@(BinOp Div y z)) = usedInTerm t
necDefine (Define x t@(BinOp Mod y z)) = usedInTerm t
necDefine (Define x t@(Call _ _)) = usedInTerm t
necDefine _ = Set.empty

necExit :: Exit (Int, [(Size, ALoc)]) (Term AVal) -> Set (Size, ALoc)
necExit (Return e) = usedInTerm e
necExit (Goto (lbl, params)) = Set.fromList params
necExit (IfElseGoto e (lbl1, params1) (lbl2, params2)) =
  Set.unions [usedInTerm e, Set.fromList params1, Set.fromList params2]


necInBlock :: Set (Size, ALoc)
           -> ([(Size, ALoc)]
              , [Define (Size, ALoc) (Term AVal)]
              , Exit (Int, [(Size, ALoc)]) (Term AVal))
           -> (Set (Size, ALoc),
              ([(Size, ALoc)]
              , [(Define (Size, ALoc) (Term AVal), Set (Size, ALoc))]
              , (Exit (Int, [(Size, ALoc)]) (Term AVal), Set (Size, ALoc))))
necInBlock nec (live, [], exit) =
  let result = Set.union (necExit exit) nec
  in
  (result, (live, [], (exit, result)))
necInBlock nec (live, d@(Define (s, asn) e) : rest, exit) =
  let (nec', (_, defs, exit')) = necInBlock nec (live, rest, exit)
      defNec = necDefine d
      thisNec = if Set.member (s, asn) nec'
                then usedInTerm e
                else Set.empty
      restNec = Set.filter ((/= asn) . snd) nec'
      currNec = Set.unions [defNec, thisNec, restNec]
  in
   (currNec, (live, (d, currNec) : defs, exit'))

necBlock :: SSA (Size, ALoc) (Term AVal) -> NeedInfo
         -> State (IntMap (Set (Size, ALoc), [(Size, ALoc)],
                           [(Define (Size, ALoc) (Term AVal),
                             Set (Size, ALoc))],
                           (Exit (Int, [(Size, ALoc)]) (Term AVal),
                            Set (Size, ALoc))))
            (Set (Size, ALoc))
necBlock (i, ssa) orig = do
    currentNec <- get
    case IntMap.lookup (fst i) currentNec of
      Just (nec, _, _, _) -> return nec
      Nothing -> do
        let (live, defs, exit) = ssa ! (fst i)
            old = case IntMap.lookup (fst i) orig of
              Just (nec, _, _, _) -> nec
              Nothing -> Set.empty
            (tempNec, (_, tempDefs, tempExit)) =
              necInBlock old (live, defs, exit)
        put $ IntMap.insert (fst i)
          (tempNec, live, tempDefs, tempExit) currentNec
        succNec <- case exit of
          Return e -> return Set.empty
          Goto lbl -> necBlock (lbl, ssa) orig
          IfElseGoto _ lbl1 lbl2 -> do
            result1 <- necBlock (lbl1, ssa) orig
            result2 <- necBlock (lbl2, ssa) orig
            return $ Set.union result1 result2
        let (result, (_, newDefs, newExit)) =
              necInBlock succNec (live, defs, exit)
        currentNec' <- get
        put $ IntMap.insert (fst i)
          (result, live, newDefs, newExit) currentNec'
        return result

needed :: SSA (Size, ALoc) (Term AVal)
       -> ((Int, [(Size, ALoc)]),
           IntMap (Set (Size, ALoc), [(Size, ALoc)],
                   [(Define (Size, ALoc) (Term AVal),
                     Set (Size, ALoc))],
                   (Exit (Int, [(Size, ALoc)]) (Term AVal),
                    Set (Size, ALoc))))
needed (i, ssa) =
  let init = execState (necBlock (i, ssa) IntMap.empty) IntMap.empty
      propogate nec =
        let result = execState (necBlock (i, ssa) nec) IntMap.empty
        in
         if result == nec
         then result
         else propogate result
  in
   (i, propogate init)



elimInBlock :: (Set (Size, ALoc), [(Size, ALoc)],
                [(Define (Size, ALoc) (Term AVal),
                  Set (Size, ALoc))],
                (Exit (Int, [(Size, ALoc)]) (Term AVal),
                 Set (Size, ALoc)))
            -> (Set (Size, ALoc), SSABlock (Size, ALoc) (Term AVal))
elimInBlock (_, live, [], (exit, nec)) = (nec, (live, [], exit))
elimInBlock (n, live, ((Define (s, a) e, nec) : rest), exit) =
  let (nec', (_, defs', exit')) = elimInBlock (n, live, rest, exit)
  in
   if not(onHeap (ALoc s a)) && Set.notMember (s, a) nec' && isPureTerm e
   then (nec', (live, defs', exit'))
   else (nec, (live, (Define (s, a) e) : defs', exit'))

elimDeadCode :: SSA (Size, ALoc) (Term AVal) -> SSA (Size, ALoc) (Term AVal)
elimDeadCode (i, ssa) = let
  (_, needInfo) = needed (i, ssa)
  in
   (i, IntMap.map (snd . elimInBlock) needInfo)
