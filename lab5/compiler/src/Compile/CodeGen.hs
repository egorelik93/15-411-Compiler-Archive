module Compile.CodeGen where

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
import Data.Monoid hiding ((<>))
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



ppDefine :: (Show val, Show asn) => Define asn (Term val) -> Doc
ppDefine (Define asn expr) =
  text (show asn) <+> text "<-" <+> ppTerm (fmap (parens . text . show) expr)

ppBlocks :: Show asn => Blocks asn (Term AVal) -> String
ppBlocks (_, blks) = show $ IntMap.foldWithKey
                     (\ i (defs, exit) doc ->
                        text (".l" ++ show i) $+$
                        nest 4 (vcat (map ppDefine defs) $+$
                                ppExit exit) $+$ doc)
                     (text "")
                     blks

ppSSA :: Show asn => SSA asn (Term AVal) -> String
ppSSA (_, blks) = show $ IntMap.foldWithKey
                  (\ i (live, defs, exit) doc ->
                    text (".l" ++ show i) <>
                    parens (hsep $ punctuate comma $ map (text . show) live)
                    $+$
                    nest 4 (vcat (map ppDefine defs) $+$
                            ppExit exit) $+$ doc)
                  (text "")
                  blks

ppExit :: (Show lbl, Show val) => Exit lbl (Term val) -> Doc
ppExit (IfElseGoto e l1 l2) =
  text "if" <+>
  parens (ppTerm (fmap (parens . text . show) e))
  <+> text "then goto" <+> text (show l1)
  <+> text "else goto" <+> text (show l2)
ppExit (Goto lbl) = text "goto" <+> text (show lbl)
ppExit (Return exp) = text "return" <+>
                      parens (ppTerm (fmap (parens . text . show) exp))

assemble :: Blocks (Size, ALoc) (Term AVal) -> SymbolGen [Instr AVal]
assemble (i, blks) = -- trace (ppBlocks (i,blks)) $
  do
    result <- IntMap.foldWithKey
              (\ i e rest -> do
                  asm <- translateAsm i e
                  rest' <- rest
                  return $ asm ++ rest')
              (return [])
              blks
    return (JMP (".l" ++ show i) : result)
                      

translateAsm :: Int -> ([Define (Size, ALoc) (Term AVal)], Exit Int (Term AVal))
             -> SymbolGen [Instr AVal]
translateAsm i (defs, exit) = do
  let defIns = concatMap translateDefine defs
  exitIns <- translateExit exit
  return $ [Label (".l" ++ show i)] ++ defIns ++ exitIns


translateExit :: Exit Int (Term AVal) -> SymbolGen [Instr AVal]
translateExit (Return exp) = return $
                             translateDefine (Define (Q, AReg 0) exp)
                             ++ [RET]
translateExit (Goto lbl) = return [JMP (".l" ++ show lbl)]
translateExit (IfElseGoto e thn' els') = let
  thn = ".l" ++ show thn'
  els = ".l" ++ show els'
  in
   case e of
     BinOp Eq e1 e2 -> return [CMPL e2 e1, JE thn, JMP els]
     BinOp NEq e1 e2 -> return [CMPL e2 e1, JNE thn, JMP els]
     BinOp Lt e1 e2 -> return [CMPL e2 e1, JL thn, JMP els]
     BinOp LtE e1 e2 -> return [CMPL e2 e1, JLE thn, JMP els]
     BinOp Gt e1 e2 -> return [CMPL e2 e1, JG thn, JMP els]
     BinOp GtE e1 e2 -> return [CMPL e2 e1, JGE thn, JMP els]
     _ -> do
       cond <- newIndex
       trueLoc <- newIndex
       let cond' = ALoc L $ ATemp cond
           trueLoc' = ALoc L $ ATemp trueLoc
       exit <- translateExit (IfElseGoto (BinOp Eq cond' trueLoc') thn' els')
       return $
         translateDefine (Define (L, ATemp cond) e)
         ++ [MOVL (AImm true) (ALoc L $ ATemp trueLoc)]
         ++ exit
            
                       
translateDefine :: Define (Size, ALoc) (Term AVal) -> [Instr AVal]
translateDefine (Define (Aggregate _, a) e) =
  translateDefine (Define (Q, a) e)
translateDefine (Define (s, a) e) =
  case e of
    BinOp Add b c
      | ALoc _ b' <- b, b' == a -> [ADDL c (ALoc s a)]
      | ALoc _ c' <- c, c' == a -> [ADDL b (ALoc s a)]
      | otherwise -> [MOVL b (ALoc s a),
                     ADDL c (ALoc s a)]
    BinOp Sub b c
      | ALoc _ b' <- b, b' == a -> [SUBL c (ALoc s a)]
      | ALoc _ c' <- c, c' == a -> [NEGQ (ALoc s a),
                                 ADDL b (ALoc s a)]
      | otherwise -> [MOVL b (ALoc s a),
                     SUBL c (ALoc s a)]
    BinOp Mul b c 
      | ALoc _ b' <- b, b' == a -> [IMULL c (ALoc s a)]
      | ALoc _ c' <- c, c' == a -> [IMULL b (ALoc s a)]
      | otherwise -> [MOVL b (ALoc s a),
                     IMULL c (ALoc s a)]
    BinOp Div b c -> [MOVL b (ALoc L $ AReg 0),
                     CLTD,
                     IDIVL c,
                     MOVL (ALoc L $ AReg 0) (ALoc s a)]
    UnOp Neg b -> [MOVL b (ALoc s a), NEGQ (ALoc s a)]
    BinOp Mod b c -> [MOVL b (ALoc L $ AReg 0),
                     CLTD,
                     IDIVL c,
                     MOVL (ALoc L $ AReg 2) (ALoc s a)]
    UnOp Nop b -> [MOVL b (ALoc s a)]
    UnOp Not b ->  [MOVL b (ALoc L a),
                   NOTL (ALoc L a),
                   ANDL (AImm 1) (ALoc L a)]
    UnOp Comp b -> [MOVL b (ALoc s a),
                  NOTL (ALoc s a)]
    BinOp Lt b c -> [MOVL (AImm false) (ALoc s a),
                    CMPL c b,
                    CMOVL (AImm true) (ALoc s a)
                   ]
    BinOp LtE b c -> [MOVL (AImm false) (ALoc s a),
                     CMPL c b,
                     CMOVLE (AImm true) (ALoc s a)
                    ]
    BinOp Gt b c -> [MOVL (AImm false) (ALoc s a),
                    CMPL c b,
                    CMOVG (AImm true) (ALoc s a)
                   ]
    BinOp GtE b c -> [MOVL (AImm false) (ALoc s a),
                     CMPL c b,
                     CMOVGE (AImm true) (ALoc s a)
                    ]
    BinOp Eq b c -> [MOVL (AImm false) (ALoc s a),
                    CMPL c b,
                    CMOVE (AImm true) (ALoc s a)
                   ]
    BinOp NEq b c -> [MOVL (AImm false) (ALoc s a),
                     CMPL c b,
                     CMOVNE (AImm true) (ALoc s a)
                    ]
    BinOp AND b c -> [MOVL b (ALoc s a),
                     ANDL c (ALoc s a)
                    ]
    BinOp XOR b c -> [MOVL b (ALoc s a),
                     XORL c (ALoc s a)
                    ]
    BinOp OR b c -> [MOVL b (ALoc s a),
                    ORL c (ALoc s a)
                   ]
    BinOp SL b c -> [MOVL b (ALoc s a),
                    SALL c (ALoc s a)
                   ]
    BinOp SR b c -> [MOVL b (ALoc s a),
                    SARL c (ALoc s a)
                   ]
    Call f params ->
      let indexedParams = reverse $ zip [1..] params
          save (i, p) = MOVL p (ALoc Q $ AArg i)
          store = fmap save indexedParams
      in
        store ++ [MOVL (AImm 0) (ALoc Q (AReg 0)),
                  CALL f params,
                  MOVL (ALoc Q (AReg 0)) (ALoc s a)
                 ]

{-

{- L1 Compiler
   Author: *[Redacted]
   Modified by: [Redacted]

   Currently just a pseudolanguage with 3-operand instructions and arbitrarily many temps.
-}
module Compile.CodeGen where

import Control.Monad.Trans.State

import Compile.Types
import qualified Data.Map as Map
import qualified Control.Monad.Free as FM
import qualified Control.MonadPlus.Free as FMP

type Alloc = (Map.Map String Int, Int)

codeGen :: AST -> [AAsm]
codeGen [FnDef _ _ stmts] = evalState program (Map.empty, 0)
  where
    program :: State Alloc [AAsm]
    program = fmap concat $ sequence $ map genStmt stmts
      

genStmt :: Stmt -> State Alloc [AAsm]
genStmt (Declare (VarDecl _ ident s) init) = do
  (a, n) <- get
  put (Map.insert ident n a, n + 1)
  case init of
    Nothing -> return []
    Just e -> genStmt $ Assign (Var ident) Nothing e s
genStmt (Return e _) = do
  (a, n) <- get
  return $ genExp (a, n + 1) e (ATemp n) ++ [ACtrl Ret $ ALoc $ ATemp n]
genStmt (Assign (Var v) o e s) = do
  (a, n) <- get
  let l = ATemp $ a Map.! v
      e' = case o of
        Nothing -> e
        Just op -> BinOp op (Val (Var v) s) e s
  return $ genExp (a, n) e' l

genExp :: Alloc -> Expr -> ALoc -> [AAsm]
genExp _ (Int n _) l = [AAsm [l] Nop [AImm $ fromIntegral n]]
genExp (a,_) (Val (Var s) _) l = [AAsm [l] Nop [ALoc $ ATemp $ a Map.! s]]
genExp (a,n) (BinOp op e1 e2 _) l = let
  i1 = genExp (a, n + 1) e1 (ATemp n)
  i2 = genExp (a, n + 2) e2 (ATemp $ n + 1)
  c  = [AAsm [l] op [ALoc $ ATemp n, ALoc $ ATemp $ n + 1]]
  in i1 ++ i2 ++ c
genExp (a,n) (UnOp op e _) l = let
  i1 = genExp (a, n + 1) e (ATemp n)
  c  = [AAsm [l] op [ALoc $ ATemp n]]
  in i1 ++ c

genTerm :: Alloc -> ALoc -> Term [AAsm] -> [AAsm]
genTerm (alloc, n) l t =
  case t of
    Int i _ -> [AAsm [l] Nop [AImm $ fromIntegral i]]
    BinOp op e1 e2 _ -> e1 ++ e2 ++ [
-}
