{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Compile.Translation where

import Prelude hiding (mapM)
import Control.Monad.Trans.State
import Data.Map (Map, (!))
import Control.Monad.Trans
import qualified Data.Map as Map
import Control.Monad.Free.Class
import qualified Control.Monad.Free as FM
import qualified Control.MonadOr.Free as FMP
import qualified Control.Monad.Trans.Free as FMF
import Data.Traversable
import Text.Parsec.Pos (SourcePos)
import Data.Monoid
import Data.Heap (MinHeap)
import qualified Data.Heap as Heap
import Debug.Trace

import Compile.Types

{-
type Alloc = (Map.Map String Int, Int)


translate :: Stmt Ident Expr -> Stmt AVal (Term AVal)-}

newtype Alloc a = Alloc (State (Int, MinHeap Int) a)
                deriving (Functor, Monad)

type Index = Map Ident ALoc

allocate :: Alloc a -> a
allocate (Alloc s) = evalState s (0, Heap.empty)

newIndex :: Alloc Int
newIndex = Alloc $ do
  (n, heap) <- get
  case Heap.view heap of
    Nothing -> do
      put (n + 1, heap)
      return n
    Just (i, heap') -> do
      put (n, heap')
      return i

freeIndex :: Int -> Alloc ()
freeIndex i = Alloc $ do
  (n, heap) <- get
  if i >= n
    then return ()
    else put (n, Heap.insert i heap)

newALoc :: Alloc ALoc
newALoc = do
  i <- newIndex
  return (ATemp i)

freeALoc :: ALoc -> Alloc ()
freeALoc (ATemp i) = freeIndex i
freeALoc _ = return ()

getALoc :: Monad a => Ident -> StateT Index a ALoc
getALoc id = do
  indexMap <- get
  return $ indexMap ! id


true = 1
false = 0

indexIdent :: Value Ident -> StateT Index Alloc AVal
indexIdent Effect = return $ AImm 1
indexIdent (Int i) = return $ AImm (fromIntegral i)
indexIdent (LVal (Var v)) = do
  indexMap <- get
  return $ ALoc $ indexMap ! v
indexIdent (Bool True) = return $ AImm true
indexIdent (Bool False) = return $ AImm false

indexExpr :: Expr (Value Ident)
          -> StateT Index Alloc (Expr AVal)
indexExpr = mapM indexIdent


indexStmt :: Stmt Ident (Expr (Value Ident)) (Expr (Value Ident))
          -> StateT Index Alloc (Stmt ALoc (Expr AVal) (Expr AVal))
indexStmt (FMP.Pure e) = fmap FMP.Pure $ indexExpr e
indexStmt (FMP.Plus s) = fmap FMP.Plus $ mapM indexStmt s
indexStmt (FMP.Free (Eval e)) = do
  e' <- indexExpr e
  return $ wrap $ Eval e'
indexStmt (FMP.Free (Assert e)) = do
  e' <- indexExpr e
  return $ wrap $ Assert e'
indexStmt (FMP.Free (Declare (VarDecl _ id _) block)) = do
  indexMap <- get
  aLoc <- lift newALoc
  put $ Map.insert id aLoc indexMap
  indexStmt block
indexStmt (FMP.Free (Assign (Var v) expr)) = do
  v' <- getALoc v
  expr' <- indexExpr expr
  return $ FMP.Free (Assign (Var v') expr')
indexStmt (FMP.Free (If e thn els)) = do
  e' <- indexExpr e
  thn' <- indexStmt thn
  els' <- indexStmt els
  return $ wrap $ If e' thn' els'
indexStmt (FMP.Free (While e blk)) = do
  e' <- indexExpr e
  blk' <- indexStmt blk
  return $ wrap $ While e' blk'


{-
translateAsm :: Stmt ALoc (Expr AVal) (Expr AVal)
             -> Alloc (Asm ALoc (String) (Expr AVal) (Expr AVal))
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

         
translateStmt :: Stmt ALoc (Expr AVal) (Expr AVal)
              -> Alloc (Stmt ALoc (Term AVal) AVal)
translateStmt (FMP.Pure e) = translateExpr e
translateStmt (FMP.Plus s) = fmap FMP.Plus $ mapM translateStmt s
translateStmt (FMP.Free (Eval e)) = do
  s <- translateExpr e
  return $ do
    e' <- s
    wrap $ Eval (UnOp Nop e')
translateStmt (FMP.Free (Assert e)) =
  translateStmt $ wrap $
  If e mempty $
  wrap $ Eval (wrap $ Call "abort" [])
translateStmt (FMP.Free (Declare _ b)) = translateStmt b
translateStmt (FMP.Free (Assign v e)) = do
  s <- translateExpr e
  return $ do
    e' <- s
    v =: UnOp Nop e'
translateStmt (FMP.Free (If e thn els)) =
  case e of
    FM.Pure (AImm b) | b == true -> translateStmt thn
                     | b == false -> translateStmt els
    _ -> do
      s <- translateExpr e
      thn' <- translateStmt thn
      els' <- translateStmt els
      return $ do
        e' <- s
        wrap $ If (UnOp Nop e') thn' els'
translateStmt (FMP.Free (While e b)) =
  case e of
    FM.Pure (AImm b) | b == false -> return mempty
    _ -> do
      s <- translateExpr e
      b' <- translateStmt b
      return $ do
        e' <- s
        wrap $ While (UnOp Nop e') $ b' <> (s >>= \_ -> mempty)
    

translateExpr :: Expr AVal
              -> Alloc (Stmt ALoc (Term AVal) AVal)
translateExpr (FM.Pure (AImm i)) = do
  store <- newALoc
  return $ do
    Var store =: UnOp Nop (AImm i)
    <> return (ALoc store)
translateExpr (FM.Pure (ALoc v)) = return $ FMP.Pure (ALoc v)
translateExpr (FM.Free (Call f params)) = do
  ss <- mapM translateExpr params
  alocs <- mapM (\_ -> newALoc) ss
  result <- newALoc
  let indexedSS = zip alocs ss
  return $ do
    foldMapDefault (\(a, s) -> do {v <- s; Var a =: UnOp Nop v}) indexedSS
    <> (Var result =: Call f (map ALoc alocs))
    <> (return $ ALoc result)
translateExpr (FM.Free (Cond e1 e2 e3)) = do
  s1 <- translateExpr e1
  s2 <- translateExpr e2
  s3 <- translateExpr e3
  result <- newALoc
  return $ do
    v1 <- s1
    let thn = do
          v2 <- s2
          Var result =: UnOp Nop v2
        els = do
          v3 <- s3
          Var result =: UnOp Nop v3
    (wrap $ If (UnOp Nop v1) thn els) <> return (ALoc result)
translateExpr (FM.Free (BinOp op e1 e2)) = do
  s1 <- translateExpr e1
  s2 <- translateExpr e2
  result <- newALoc
  return $ do
    v1 <- s1
    v2 <- s2
    Var result =: BinOp op v1 v2
    <> return (ALoc result)
translateExpr (FM.Free (UnOp op e)) = do
  s <- translateExpr e
  result <- newALoc
  return $ do
    v <- s
    Var result =: (UnOp op v)
    <> return (ALoc result)

translate :: AST Ident (Stmt Ident (Expr (Value Ident)) (Expr (Value Ident)))
          -> Alloc (Map Ident ([ALoc], Stmt ALoc (Term AVal) AVal))
translate ((FnDef (VarDecl _ id _) params stmt) : rest) = do
  let newParam (VarDecl _ p _) = do
        v <- newALoc
        return (p, v)
  paramPairs <- mapM newParam params
  let paramLocs = map snd paramPairs
      paramCtx = Map.fromList paramPairs
  result <- evalStateT (indexStmt stmt) paramCtx
            >>= translateStmt
  let ctx = Map.singleton id (paramLocs, result)
  rest' <- translate rest
  return $ Map.unionWithKey
    (\k _ _ -> error $
               "Disallowed repeated function definition of " ++ k)
    ctx rest'
translate (_ : rest) = translate rest
translate [] = return Map.empty

codeGen :: Stmt ALoc (Term AVal) AVal -> Alloc [AAsm]
codeGen (FMP.Pure v) = return [ACtrl Ret v]
codeGen (FMP.Plus s) = fmap concat $ mapM codeGen s
codeGen (FMP.Free (Eval e)) = return []
codeGen (FMP.Free (Declare _ b)) = codeGen b
codeGen (FMP.Free (Assign (Var v) (Call f params))) = do
  let indexedParams = reverse $ zip [1..] params
      save (i, p) = AAsm [AArg i] Nop [p]
      store = map save indexedParams
  return $ store ++
    [AAsm [AReg 0] Nop [AImm 0],
     ACall f params,
     AAsm [v] Nop [ALoc $ AReg 0]
    ]
codeGen (FMP.Free (Assign (Var v) (BinOp op e1 e2))) =
  return [AAsm [v] op [e1, e2]]
codeGen (FMP.Free (Assign (Var v) (UnOp op e))) =
  return [AAsm [v] op [e]]
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
      
  return $ [AAsm [cond] op [e1, e2],
            AAsm [trueLoc] Nop [AImm true],
            AIfGoto (ALoc cond) Eq (ALoc trueLoc) l1, AGoto l2,
            ALabel l1]
    ++ thn' ++ [AGoto done]
    ++ [ALabel l2] ++ els' ++ [AGoto done, ALabel done]
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
      
  return $ [AAsm [cond] op [e],
            AAsm [trueLoc] Nop [AImm true],
            AIfGoto (ALoc cond) Eq (ALoc trueLoc) l1, AGoto l2,
            ALabel l1]
    ++ thn' ++ [AGoto done]
    ++ [ALabel l2] ++ els' ++ [AGoto done, ALabel done]
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
  return $ [ALabel loop,
            AAsm [cond] op [e1, e2],
            AAsm [trueLoc] Nop [AImm true],
            AIfGoto (ALoc cond) NEq (ALoc trueLoc) done]
    ++ b'
    ++ [AGoto loop, ALabel done]
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
  return $ [ALabel loop,
            AAsm [cond] op [e],
            AAsm [trueLoc] Nop [AImm true],
            AIfGoto (ALoc cond) NEq (ALoc trueLoc) done]
    ++ b'
    ++ [AGoto loop, ALabel done]
