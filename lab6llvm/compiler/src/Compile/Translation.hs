module Compile.Translation where

import Prelude hiding (mapM, sequence, msum)
import Control.Monad.Trans.State
import Data.Map (Map, (!))
import Control.Monad.Trans
import qualified Data.Map as Map
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
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
import Data.List (find)
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Debug.Trace

import Compile.Types
import Compile.Types.Assembly
import Compile.SymbolGen
import Compile.TypeChecker (subst, subst', subst'')

{-
type SymbolGen = (Map.Map String Int, Int)


translate :: Stmt Ident Expr -> Stmt AVal (Term AVal)-}

type Index = (Map Ident (C0Type Ident), Map Ident (ALoc, C0Type Ident))

newALoc :: SymbolGen ALoc
newALoc = do
  i <- newIndex
  return (ATemp i)

freeALoc :: ALoc -> SymbolGen ()
freeALoc (ATemp i) = freeIndex i
freeALoc _ = return ()

getALoc :: Monad a => Ident -> StateT Index a (ALoc, C0Type Ident)
getALoc id = do
  (_, indexMap) <- get
  case Map.lookup id indexMap of
    Just v -> return v
    Nothing -> error $ "Cannot find variable of name " ++ id


true = 1
false = 0

sizeOf :: C0Type Ident -> Size
sizeOf IntType = L
sizeOf BoolType = L
sizeOf (PointerType _) = Q
sizeOf (ArrayType _) = Q
sizeOf (StructType _ fs) = Aggregate $ map (\(VarDecl t _ _) -> sizeOf t) fs
sizeOf VoidType = L
sizeOf AnyType = Q
sizeOf s = error $ "Undefined size for " ++ show (ppType s)

indexLValue :: LValue Ident (TExpr (Value Ident))
            -> StateT Index SymbolGen (TExpr AVal)
indexLValue (Var v) = do
  (l, t) <- getALoc v
  return (return $ env t $ ALoc (sizeOf t) l)
indexLValue (Pointer v) = do
  v' <- indexLValue v
  let PointerType t = typeOf v'
  (ts, _) <- get
  return (wrap $ EnvT (subst'' ts t) $ Deref v')
indexLValue (Index v e) = do
  v' <- indexLValue v
  e' <- indexExpr e
  let ArrayType t = typeOf v'
  (ts, _) <- get
  return (wrap $ EnvT (subst'' ts t) $ Elt v' e')
indexLValue (Field v f) = do
  v' <- indexLValue v
  let StructType t fs = typeOf v'
      Just (VarDecl t' _ _) = find (\(VarDecl _ f' _) -> f == f') fs
  return (wrap $ EnvT t' $ Get v' f)

indexIdent :: Value Ident -> StateT Index SymbolGen (TExpr AVal)
indexIdent Effect = return $ return $ env VoidType $ AImm 1
indexIdent (Int i) = return $ return $ env IntType $ AImm (fromIntegral i)
indexIdent (VarVal v) = do
  (l, t) <- getALoc v
  return (return $ env t $ ALoc (sizeOf t) l)
indexIdent (Bool True) = return $ return $ env BoolType $ AImm true
indexIdent (Bool False) = return $ return $ env BoolType $ AImm false
indexIdent NULL = return $ return $ env (PointerType AnyType) $ AImm 0

indexExpr :: TExpr (Value Ident)
          -> StateT Index SymbolGen (TExpr AVal)
indexExpr (FM.Pure i) = indexIdent $ snd $ runEnv i
indexExpr (FM.Free e) = fmap wrap $ mapM indexExpr e
  
indexStmt :: Bool -> TStmt Ident
          -> StateT Index SymbolGen (Stmt ALoc (TExpr AVal) (TExpr AVal))
indexStmt _ (FMP.Pure e) = fmap FMP.Pure $ indexExpr e
indexStmt safe (FMP.Plus s) = fmap FMP.Plus $ mapM (indexStmt safe) s
indexStmt _ (FMP.Free (Eval e)) = do
  e' <- indexExpr e
  return $ wrap $ Eval e'
indexStmt _ (FMP.Free (Assert e)) = do
  e' <- indexExpr e
  return $ wrap $ Assert e'
indexStmt safe (FMP.Free (Declare (VarDecl t id _) block)) = do
  (ts, indexMap) <- get
  aLoc <- lift newALoc
  put (ts, Map.insert id (aLoc, t) indexMap)
  indexStmt safe block
indexStmt _ (FMP.Free (Assign (Var v) expr)) = do
  (_, indexMap) <- get
  let (v', _) = case Map.lookup v indexMap of
        Just e -> e
        Nothing -> error $ "Cannot find variable of name " ++ v
  expr' <- indexExpr expr
  return $ FMP.Free (Assign (Var v') expr')
indexStmt _ (FMP.Free (Assign (Pointer v) expr)) = do
  v' <- indexLValue v
  pointer <- lift newALoc
  expr' <- indexExpr expr
  return $
    (Var pointer =: v')
    <> (Pointer (Var pointer) =: expr')
indexStmt _ (FMP.Free (Assign (Index v e) expr)) = do
  v' <- indexLValue v
  e' <- indexExpr e
  base <- lift newALoc
  expr' <- indexExpr expr
  return $
    (Var base =: v')
    <> (Index (Var base) e' =: expr')
indexStmt safe (FMP.Free (Assign (Field v f) expr)) = do
  v' <- indexLValue v
  expr' <- indexExpr expr
  base <- lift newALoc
  (ts, _) <- get
  let StructType t fs = subst'' ts $ typeOf v'
      findOffset [] = error $ "Field " ++ f ++ " not found despite "
                      ++ " successful type check"
      findOffset (VarDecl t' f' _ : fs)
        | f == f' = 0
        | otherwise = bytes (sizeOf $ subst'' ts t') + findOffset fs
      offset = findOffset fs
      null = return $ env (PointerType (StructType t fs)) $ AImm 0
      segFault = return $ wrap $ EnvT AnyType $ Deref null
      baseE = return $ env (PointerType (StructType t fs)) $ ALoc Q base
  if safe then
    return $
     (Var base =: v')
     <> (wrap $
         If (wrap $ EnvT BoolType $ BinOp Eq baseE null)
         segFault
         (Var (AOffset offset (ALoc Q base)) =: expr'))
    else return $
         (Var base =: v')
         <> (Var (AOffset offset (ALoc Q base)) =: expr')
{-
indexStmt (FMP.Free (Assign (Field (Index v e) f) expr)) = do
  v' <- indexLValue v
  e' <- indexExpr e
  expr' <- indexExpr expr
  index <- lift newALoc
  len <- lift newALoc
  array <- lift newALoc
  (ts, _) <- get
  let ArrayType (StructType id fs) = subst' ts $ typeOf v'
      findOffset [] = error $ "Field " ++ f ++ " not found despite "
                      ++ " successful type check"
      findOffset (VarDecl t' f' _ : fs)
        | f == f' = 0
        | otherwise = bytes (sizeOf t') + findOffset fs
      offset = findOffset fs
      size = return $ env IntType $ AImm $ bytes $ sizeOf (StructType "" fs)
      null = return $ env t $ AImm 0
      zero = return $ env IntType $ AImm 0
      segFault = return $ wrap $ EnvT AnyType $ Deref null
      indexE = return $ env IntType $ ALoc L index
      indexQ = return $ env IntType $ ALoc Q index
      arrayE = return $ env (ArrayType (StructType id fs)) $ ALoc Q array
      lenE = return $ env IntType $ ALoc L len
      t = PointerType (StructType id fs)
  return $
    (Var array =: v')
    <> (Var index =: e')
    <> (wrap $ If (wrap $ EnvT BoolType $ BinOp GtE indexE zero)
        (
          (Var len =: (return $ env IntType $
                       ALoc L (AOffset (-8) (ALoc Q array))))
          <> (wrap $ If (wrap $ EnvT BoolType $ BinOp Lt indexE lenE)
              ((Var index =: wrap (EnvT t $ BinOp Mul indexE size))
               <> (Var index =: wrap (EnvT t $ BinOp Add indexQ arrayE))
               <> (Var (AOffset offset (ALoc Q index)) =: expr')
              )
              segFault
             ))
        segFault
       )
-}
{-
indexStmt (FMP.Free (Assign (Field (Pointer v) f) expr)) = do
  v' <- indexLValue v
  expr' <- indexExpr expr
  base <- lift newALoc
  (ts, _) <- get
  let PointerType (StructType t fs) = subst' ts $ typeOf v'
      findOffset [] = error $ "Field " ++ f ++ " not found despite "
                      ++ " successful type check"
      findOffset (VarDecl t' f' _ : fs)
        | f == f' = 0
        | otherwise = bytes (sizeOf t') + findOffset fs
      offset = findOffset fs
      null = return $ env (PointerType (StructType t fs)) $ AImm 0
      segFault = return $ wrap $ EnvT AnyType $ Deref null
      baseE = return $ env (PointerType (StructType t fs)) $ ALoc Q base
  return $
    (Var base =: v')
    <> (wrap $
        If (wrap $ EnvT BoolType $ BinOp Eq baseE null)
        segFault
        (Var (AOffset offset (ALoc Q base)) =: expr'))
-}
indexStmt safe (FMP.Free (If e thn els)) = do
  e' <- indexExpr e
  thn' <- indexStmt safe thn
  els' <- indexStmt safe els
  return $ wrap $ If e' thn' els'
indexStmt safe (FMP.Free (While e blk)) = do
  e' <- indexExpr e
  blk' <- indexStmt safe blk
  return $ wrap $ While e' blk'


{-
translateAsm :: Stmt ALoc (Expr AVal) (Expr AVal)
             -> SymbolGen (Asm ALoc (String) (Expr AVal) (Expr AVal))
translateAsm (FMP.Pure e) = return $ FMP.Pure e
translateAsm (FMP.Plus s) = fmap FMP.Plus $ mapM translateAsm s
translateAsm (FMP.Free s) =
  case s of
       Declare _ b -> translateAsm b
       Assign (LValue v) e -> return $ wrap $ FMF.Pure $ Define v e
       If e thn els -> do
         thn' <- translateAsm thn
         els' <- translateAsm els
         i1 <- newIndex
         i2<- newIndex
         i3 <- newIndex
         let l1 = ".l" ++ show i1
             l2 = ".l" ++ show i2
             l3 = ".l" ++ show i3
             done = wrap (FMF.Pure $ Goto l3)
             end = wrap (FMF.Pure $ Goto NextLine)
             -- thnUsed = Set.toList $ used thn'
             -- elsUsed = Set.toList $ used els'
         return $
           wrap (FMF.Pure $ IfElseGoto e l1 l2)
           <> wrap (FMF.Free $ Labeled l1 thn' done)
           <> wrap (FMF.Free $ Labeled l2 els' done)
           <> wrap (FMF.Free $ Labeled l3 mempty end)
       While e blk -> do
         blk' <- translateAsm blk
         i1 <- newIndex
         i2 <- newIndex
         let l1 = ".l" ++ show i1
             l2 = ".l" ++ show i2
             cond = wrap (FMF.Pure $ IfElseGoto e l1 l2)
             end = wrap (FMF.Pure $ Goto NextLine)
         return $
           cond
           <> wrap (FMF.Free $ Labeled l1 blk' cond)
           <> wrap (FMF.Free $ Labeled l2 mempty end)
       Eval e -> do
         result <- newALoc
         return $ FMF.Pure $ Define result e-}

         
translateStmt :: Bool -> Stmt ALoc (TExpr AVal) (TExpr AVal)
              -> SymbolGen (Stmt (Size, ALoc) (Term AVal) AVal)
translateStmt safe (FMP.Pure e) = translateExpr safe e
translateStmt safe (FMP.Plus s) = fmap FMP.Plus $ mapM (translateStmt safe) s
translateStmt safe (FMP.Free (Eval e)) = do
  s <- translateUpToOp safe e
  result <- newALoc
  let size = sizeOf $ typeOf e
  return $ do
    e' <- s
    (Var (size, result) =: e')
    <> (wrap $ Eval $ UnOp Nop (ALoc (sizeOf $ typeOf e) result))
translateStmt safe (FMP.Free (Assert e)) =
  translateStmt safe $ wrap $
  If e mempty $
  wrap $ Eval (wrap $ EnvT VoidType $ Call "abort" [])
translateStmt safe (FMP.Free (Declare _ b)) = translateStmt safe b
translateStmt safe (FMP.Free (Assign (Var v) e)) = do
  s <- translateUpToOp safe e
  let size = sizeOf $ typeOf e
  return $ do
    e' <- s
    Var (size, v) =: e'
translateStmt safe (FMP.Free (Assign (Pointer (Var v)) e)) = do
  s <- translateUpToOp safe e
  let size = sizeOf $ typeOf e
  return $ do
    e' <- s
    Var (size, AAddr (ALoc Q v)) =: e'
translateStmt safe (FMP.Free (Assign (Index (Var v) i) e)) = do
  si <- translateExpr safe i
  se <- translateUpToOp safe e
  addr <- newALoc
  null <- newALoc
  let segFault =
        (Var (Q, null) =: UnOp Nop (AImm 0))
        <> (Var (Q, null) =: UnOp Nop (ALoc Q (AAddr (ALoc Q null))))
        <> (return $ AImm 0)
      size = sizeOf $ typeOf e
  len <- newALoc
  if safe
    then return $ do
      i' <- si
      e' <- se
      (
        (Var (Q, addr) =: BinOp Sub (ALoc Q v) (AImm 8))
        <>
        (Var (L, len) =: UnOp Nop (ALoc L $ AAddr (ALoc Q addr)))
        <>
        wrap (If (BinOp GtE i' (AImm 0))
              (wrap $ If (BinOp Lt i' (ALoc L len))
               (
                 (Var (Q, addr) =: BinOp Mul i' (AImm $ bytes size))
                 <>
                 (Var (Q, addr) =: BinOp Add (ALoc Q addr) (ALoc Q v))
                 <>
                 (Var (size, AAddr (ALoc Q addr)) =: e')
               )
               segFault
              )
              segFault)
        )
    else return $ do
      i' <- si
      e' <- se
      ((Var (Q, addr) =: BinOp Mul i' (AImm $ bytes size))
       <> (Var (Q, addr) =: BinOp Add (ALoc Q addr) (ALoc Q v))
       <> (Var (size, AAddr (ALoc Q addr)) =: e'))
translateStmt safe (FMP.Free (If e thn els)) = do
  e' <- translateUpToOp safe e
  thn' <- translateStmt safe thn
  els' <- translateStmt safe els
  return $ do
    s <- e'
    case s of
      UnOp Nop (AImm b)
        | b == true -> thn'
        | b == false -> els'
      _ -> wrap $ If s thn' els'
{-
  case e of
    FM.Pure (snd . runEnv -> AImm b)
      | b == true -> translateStmt thn
      | b == false -> translateStmt els
    FM.Pure (snd . runEnv -> a) -> do
      thn' <- translateStmt thn
      els' <- translateStmt els
      return $
        wrap $ If (UnOp Nop a) thn' els'
    FM.Free (snd . runEnvT -> UnOp Not e) ->
      translateStmt (FMP.Free (If e els thn))
    FM.Free (snd . runEnvT -> e) -> do
      s <- mapM translateExpr e
      thn' <- translateStmt thn
      els' <- translateStmt els
      return $ do
        e' <- sequence s
        wrap $ If e' thn' els'
-}
translateStmt safe (FMP.Free (While e b)) = do
  e' <- translateUpToOp safe e
  b' <- translateStmt safe b
  return $ do
    t <- e'
    case t of
      UnOp Nop (AImm b) | b == false -> mempty
      _ -> wrap $ While t $ b' <> (e' >>= \_ -> mempty)
{-
  case e of
    FM.Pure (snd . runEnv -> AImm b)
      | b == false -> return mempty
    FM.Pure (snd . runEnv -> a) -> do
      b' <- translateStmt b
      return $
        wrap $ While (UnOp Nop a) $ b'
    FM.Free (snd . runEnvT -> e) -> do
      s <- mapM translateExpr e
      b' <- translateStmt b
      return $ do
        e' <- s
        wrap $ While e' $ b' <> (s >>= \_ -> mempty)
-}
    

translateExpr :: Bool -> TExpr AVal
              -> SymbolGen (Stmt (Size, ALoc) (Term AVal) AVal)
translateExpr safe (FM.Pure i) =
  case runEnv i of
    (t, AImm i) -> do
      store <- newALoc
      return $ do
        (Var (sizeOf t, store) =: UnOp Nop (AImm i))
        <> return (ALoc (sizeOf t) store)
    (t, ALoc s (AAddr v)) -> do
      pointer <- newALoc
      result <- newALoc
      e <- translateUpToOp safe (FM.Pure $ env (PointerType t) v)
      return $ do
        v <- e
        (Var (Q, pointer) =: v)
        <> (Var (sizeOf t, result) =: Deref (ALoc Q pointer))
        <> return (ALoc s result)
    (_, ALoc s v) -> return $ FMP.Pure (ALoc s v)
translateExpr safe (FM.Free (runEnvT -> (t, Call f params))) = do
  ss <- mapM (translateUpToOp safe) params
  alocs <- mapM (\_ -> newALoc) ss
  result <- newALoc
  let sizes = map (sizeOf . typeOf) params
      indexedSS = zip3 alocs ss sizes
  return $ do
    foldMapDefault (\(a, ss, s) -> do {v <- ss; Var (s, a) =: v}) indexedSS
    <> (Var (sizeOf t, result) =: 
        Call f (map (\(l, _, s) -> ALoc s l) indexedSS))
    <> (return $ ALoc (sizeOf t) result)
translateExpr safe (FM.Free (runEnvT -> (t, Cond e1 e2 e3))) = do
  s1 <- translateUpToOp safe e1
  s2 <- translateUpToOp safe e2
  s3 <- translateUpToOp safe e3
  let size = sizeOf t
  result <- newALoc
  return $ do
    v1 <- s1
    let thn = do
          v2 <- s2
          Var (size, result) =: v2
        els = do
          v3 <- s3
          Var (size, result) =: v3
    (wrap $ If v1 thn els) <> return (ALoc size result)
translateExpr safe (FM.Free (runEnvT -> (t, BinOp op e1 e2))) = do
  s1 <- translateExpr safe e1
  s2 <- translateExpr safe e2
  result <- newALoc
  return $ do
    v1 <- s1
    v2 <- s2
    (Var (sizeOf t, result) =: BinOp op v1 v2)
    <> return (ALoc (sizeOf t) result)
translateExpr safe (FM.Free (runEnvT -> (t, UnOp op e))) = do
  s <- translateExpr safe e
  result <- newALoc
  return $ do
    v <- s
    (Var (sizeOf t, result) =: UnOp op v)
    <> return (ALoc (sizeOf t) result)
translateExpr safe (FM.Free (runEnvT -> (t, Deref e))) = do
  e' <- translateExpr safe e
  result <- newALoc
  pointer <- newALoc
  return $ do
    v <- e'
    (Var (Q, pointer) =: UnOp Nop v)
    <> (case sizeOf t of
           Aggregate _ -> return $ ALoc Q pointer
           s -> (Var (s, result) =:
                 UnOp Nop (ALoc s $ AAddr (ALoc Q pointer)))
                <> return (ALoc s result)
       )
translateExpr safe (FM.Free (runEnvT -> (_, Alloc t))) = do
  let size = bytes $ sizeOf t
      t' = PointerType t'
  case size of
    0 -> do
      i <- newIndex
      return $ return (AImm i)
    _ -> translateExpr safe $ wrap $ EnvT t' $
         Call "calloc" [return $ env IntType $ AImm size,
                        return $ env IntType $ AImm 1]
translateExpr safe (FM.Free (runEnvT -> (_, AllocArray t e))) = do
  let size = bytes $ sizeOf t
  e' <- translateExpr safe e
  n' <- newALoc
  a' <- newALoc
  len <- newALoc
  array <- newALoc
  null <- newALoc
  s <- translateExpr safe $ wrap $ EnvT (ArrayType t) $
       Call "calloc" [return $ env IntType $ ALoc L n',
                      return $ env IntType $ AImm 1]
  let segFault =
        (Var (Q, null) =: UnOp Nop (AImm 0))
        <> (Var (Q, null) =: UnOp Nop (ALoc Q (AAddr (ALoc Q null))))
        <> (return $ AImm 0)
      evalLength =
        if safe then
          do
            n <- e'
            ((Var (L, len) =: UnOp Nop n)
             <> (wrap $ If (BinOp Lt (ALoc L len) (AImm 0))
                 segFault mempty)
             <> (Var (L, n') =: BinOp Mul (AImm size) (ALoc L len))
             <> (Var (L, n') =: BinOp Add (AImm 8) (ALoc L n')))
        else do
          n <- e'
          ((Var (L, len) =: UnOp Nop n)
           <> (Var (L, n') =: BinOp Mul (AImm size) (ALoc L len)))
      alloc = do
        a <- s
        ((Var (Q, array) =: UnOp Nop a)
         <> (Var (L, AAddr (ALoc Q array)) =: UnOp Nop (ALoc L len))
         <> (Var (Q, a') =: BinOp Add (AImm 8) a)
         <> (return (ALoc Q a'))
          )
  if safe
    then return (evalLength <> alloc)
    else return (evalLength <> s)
translateExpr safe (FM.Free (runEnvT -> (t, Elt e i))) = do
  e' <- translateExpr safe e
  i' <- translateExpr safe i
  size <- newALoc
  store <- newALoc
  addr <- newALoc
  null <- newALoc
  let segFault =
        (Var (Q, null) =: UnOp Nop (AImm 0))
        <> (Var (Q, null) =: UnOp Nop (ALoc Q (AAddr (ALoc Q null))))
        <> (return $ AImm 0)
      a' = ALoc Q store
  return $
    if safe then do
      a <- e'
      index <- i'
      ((Var (sizeOf $ typeOf e, store) =: UnOp Nop a)
       <>
       (Var (L, size) =: UnOp Nop (ALoc L $ AOffset (-8) a'))
       <>
       (wrap $ If (BinOp GtE index (AImm 0))
        (wrap $ If (BinOp Lt index (ALoc L size))
         ((Var (Q, addr) =: BinOp Mul index (AImm $ bytes (sizeOf t)))
          <> (Var (Q, addr) =: BinOp Add (ALoc Q addr) a')
          <> (case sizeOf t of
                 Aggregate _ -> return $ ALoc Q addr
                 s -> return $ ALoc s $ AAddr (ALoc Q addr)))
         segFault
        )
        segFault
       ))
    else do
      a <- e'
      index <- i'
      ((Var (sizeOf $ typeOf e, store) =: UnOp Nop a)
       <> (Var (Q, addr) =: BinOp Mul index (AImm $ bytes (sizeOf t)))
       <> (Var (Q, addr) =: BinOp Add (ALoc Q addr) a')
       <> (case sizeOf t of
              Aggregate _ -> return $ ALoc Q addr
              s -> return $ ALoc s $ AAddr (ALoc Q addr)))
translateExpr safe (FM.Free (runEnvT -> (t, Get e f))) = do
  e' <- translateExpr safe e
  null <- newALoc
  temp <- newALoc
  let StructType _ fs = typeOf e
      findOffset [] = error $ "Field " ++ f ++ " not found despite "
                      ++ " successful type check"
      findOffset (VarDecl t' f' _ : fs)
        | f == f' = 0
        | otherwise = bytes (sizeOf t') + findOffset fs
      offset = findOffset fs
      segFault = (Var (Q, null) =: UnOp Nop (AImm 0))
                 <> (Var (Q, null) =: UnOp Nop (ALoc Q (AAddr (ALoc Q null))))
                 <> (return $ AImm 0)
  result <- newALoc
  return $ do
    v <- e'
    ((Var (Q, temp) =: UnOp Nop v)
     <>
     (if safe then
        (wrap $ If (BinOp Eq (ALoc Q temp) (AImm 0)) segFault mempty)
      else mempty)
     <>
     case sizeOf t of
       Aggregate _ -> (Var (Q, result) =: BinOp Add (AImm offset)
                       (ALoc Q temp))
                      <> return (ALoc Q result)
       s ->
         (Var (s, result) =: UnOp Nop (ALoc s $ AOffset offset (ALoc Q temp)))
         <> return (ALoc s result))

translateUpToTerm :: Bool -> TExpr AVal
                  -> SymbolGen (Stmt (Size, ALoc) (Term AVal) (Term AVal))
translateUpToTerm _ (FM.Pure i) = return $ return $ UnOp Nop $ snd $ runEnv i
translateUpToTerm safe (FM.Free e) =
  mapM (translateExpr safe) (snd $ runEnvT e) >>= (return . sequence)

translateUpToOp :: Bool -> TExpr AVal
                -> SymbolGen (Stmt (Size, ALoc) (Term AVal) (Term AVal))
translateUpToOp safe e@(FM.Pure i) = translateUpToTerm safe e
translateUpToOp safe e@(FM.Free t) =
  case snd $ runEnvT t of
    BinOp _ _ _ -> translateUpToTerm safe e
    UnOp Nop e' -> translateUpToOp safe e'
    UnOp _ _ -> translateUpToTerm safe e
    _ -> do
      e' <- translateExpr safe e
      return $ fmap (UnOp Nop) e'
      
  

translate :: Bool -> Map Ident (C0Type Ident)
          -> ([VarDecl Ident], C0Type Ident, TStmt Ident)
          -> SymbolGen ([AVal], Size, Stmt (Size, ALoc) (Term AVal) AVal)
translate safe ts (params, out, stmt) = do
  let newParam (VarDecl t p _) = do
        v <- newALoc
        return (p, (v, t))
  paramPairs <- mapM newParam params
  let paramLocs = map (\(_, (v, t)) -> ALoc (sizeOf t) v) paramPairs
      paramCtx = Map.fromList paramPairs
  result <- evalStateT (indexStmt safe stmt) (ts, paramCtx)
            >>= translateStmt safe
  return (paramLocs, sizeOf out, result)



codeGen exit (FMP.Pure v) = codeGen' exit [FMP.Pure v]
codeGen exit (FMP.Free s) = codeGen' exit [FMP.Free s]
codeGen exit (FMP.Plus ss) = codeGen' exit ss


codeGen' :: Exit Int (Term AVal)
         -> [Stmt (Size, ALoc) (Term AVal) AVal]
         -> SymbolGen (Blocks (Size, ALoc) (Term AVal))
codeGen' exit (FMP.Pure v : _) = do
  i <- newIndex
  return (i, IntMap.singleton i ([], Return (UnOp Nop v)))
codeGen' exit [] = do
  i <- newIndex
  return (i, IntMap.singleton i ([], exit))
codeGen' exit (FMP.Plus s : ss) = codeGen' exit (s ++ ss)
codeGen' exit (FMP.Free e : ss) =
  case e of
    Eval _ -> codeGen' exit ss
    Declare _ b -> codeGen exit b
    Assign (Var (s, v)) e -> do
      (i, ss') <- codeGen' exit ss
      let s' = case s of
            Aggregate _ -> Q
            _ -> s
      return (i, IntMap.update (\(defs, exit) ->
                                 Just (Define (s', v) e : defs, exit))
                 i ss')
    If e thn els -> do
      i1 <- newIndex
      (exit, ss') <- codeGen' exit ss
      let exit' = Goto exit
      (i2, thn') <- codeGen exit' thn
      (i3, els') <- codeGen exit' els
      let cond = IntMap.singleton i1 ([], IfElseGoto e i2 i3)
      return (i1, IntMap.unions [cond, thn', els', ss'])

    While e blk -> do
      i1 <- newIndex
      i2 <- newIndex
      (exit, ss') <- codeGen' exit ss
      let exit' = Goto i2
      (loop, blk') <- codeGen exit' blk 
      let start = IntMap.singleton i1 ([], Goto i2)
          cond = IntMap.singleton i2 ([], IfElseGoto e loop exit)
      return (i1, IntMap.unions [ss', blk', start, cond])

{-
codeGen :: Stmt ALoc (Term AVal) AVal -> SymbolGen (Seq AAsm)
codeGen (FMP.Pure v) = return $ Seq.singleton $ ACtrl Ret v
codeGen (FMP.Plus s) = fmap msum $ mapM codeGen s
codeGen (FMP.Free (Eval e)) = return Seq.empty
codeGen (FMP.Free (Declare _ b)) = codeGen b
codeGen (FMP.Free (Assign (Var v) (Call f params))) = do
  let indexedParams = Seq.reverse $ Seq.fromList $ zip [1..] params
      save (i, p) = AAsm [AArg i] Q Nop [p]
      store = fmap save indexedParams
  return $ store <> Seq.fromList
    [AAsm [AReg 0] Q Nop [AImm 0],
     ACall f params,
     AAsm [v] Q Nop [ALoc Q $ AReg 0]
    ]
codeGen (FMP.Free (Assign (Var v) (BinOp op e1 e2))) =
  return $ Seq.singleton $ AAsm [v] Q op [e1, e2]
codeGen (FMP.Free (Assign (Var v) (UnOp op e)))
  | onHeap (ALoc Q v) = return $ Seq.singleton $ AAsm [v] (size e) op [e]
  | otherwise = return $ Seq.singleton $ AAsm [v] Q op [e]
codeGen (FMP.Free (If (BinOp op e1 e2) thn els))
  | op `elem` [Eq, NEq, Gt, GtE, Lt, LtE] = do
    i1 <- newIndex
    i2<- newIndex
    i3 <- newIndex
    thn' <- codeGen thn
    els' <- codeGen els
    let l1 = ".l" ++ show i1
        l2 = ".l" ++ show i2
        done = ".l" ++ show i3
      
    return $ Seq.fromList [AIfGoto e1 op e2 l1, AGoto l2,
                           ALabel l1]
      <> thn' <> Seq.singleton (AGoto done)
      <> Seq.singleton (ALabel l2) <> els'
      <> Seq.fromList [AGoto done, ALabel done]
codeGen (FMP.Free (If (BinOp op e1 e2) thn els)) = do
  i1 <- newIndex
  i2<- newIndex
  i3 <- newIndex
  trueLoc <- newALoc
  thn' <- codeGen thn
  els' <- codeGen els
  cond <- newALoc
  freeALoc trueLoc
  freeALoc cond
  let l1 = ".l" ++ show i1
      l2 = ".l" ++ show i2
      done = ".l" ++ show i3
      
  return $ Seq.fromList
    [AAsm [cond] L op [e1, e2],
     AAsm [trueLoc] L Nop [AImm true],
     AIfGoto (ALoc L cond) Eq (ALoc L trueLoc) l1, AGoto l2,
     ALabel l1]
    <> thn' <> Seq.singleton (AGoto done)
    <> Seq.singleton (ALabel l2) <> els'
    <> Seq.fromList [AGoto done, ALabel done]
codeGen (FMP.Free (If (UnOp Not e) thn els)) =
  codeGen (FMP.Free $ If (UnOp Nop e) els thn)
codeGen (FMP.Free (If (UnOp op e) thn els)) = do
  i1 <- newIndex
  i2<- newIndex
  i3 <- newIndex
  trueLoc <- newALoc
  thn' <- codeGen thn
  els' <- codeGen els
  cond <- newALoc
  freeALoc trueLoc
  freeALoc cond
  let l1 = ".l" ++ show i1
      l2 = ".l" ++ show i2
      done = ".l" ++ show i3
      
  return $ Seq.fromList
    [AAsm [cond] L op [e],
     AAsm [trueLoc] L Nop [AImm true],
     AIfGoto (ALoc L cond) Eq (ALoc L trueLoc) l1, AGoto l2,
     ALabel l1]
    <> thn' <> Seq.singleton (AGoto done)
    <> Seq.singleton (ALabel l2) <> els'
    <> Seq.fromList [AGoto done, ALabel done]
codeGen (FMP.Free (While (BinOp op e1 e2) b))
  | op `elem` [Eq, NEq, Gt, GtE, Lt, LtE] = do
    i1 <- newIndex
    i2 <- newIndex
    b' <- codeGen b
    let loop = ".l" ++ show i1
        start = ".l" ++ show i2
    return $ Seq.fromList [AGoto start, ALabel loop]
      <> b'
      <> Seq.fromList [ALabel start, AIfGoto e1 op e2 loop]
codeGen (FMP.Free (While (BinOp op e1 e2) b)) = do
  i1 <- newIndex
  i2 <- newIndex
  cond <- newALoc
  b' <- codeGen b
  trueLoc <- newALoc
  freeALoc cond
  freeALoc trueLoc
  let loop = ".l" ++ show i1
      done = ".l" ++ show i2
  return $ Seq.fromList
    [ALabel loop,
     AAsm [cond] L op [e1, e2],
     AAsm [trueLoc] L Nop [AImm true],
     AIfGoto (ALoc L cond) NEq (ALoc L trueLoc) done]
    <> b'
    <> Seq.fromList [AGoto loop, ALabel done]
codeGen (FMP.Free (While (UnOp op e) b)) = do
  i1 <- newIndex
  i2 <- newIndex
  cond <- newALoc
  b' <- codeGen b
  trueLoc <- newALoc
  freeALoc trueLoc
  freeALoc cond
  let loop = ".l" ++ show i1
      done = ".l" ++ show i2
  return $ Seq.fromList
    [ALabel loop,
     AAsm [cond] L op [e],
     AAsm [trueLoc] L Nop [AImm true],
     AIfGoto (ALoc L cond) NEq (ALoc L trueLoc) done]
    <> b'
    <> Seq.fromList [AGoto loop, ALabel done]
-}
