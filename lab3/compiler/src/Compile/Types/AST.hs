{-# LANGUAGE OverlappingInstances #-}

{- L1 Compiler
   Author: *[Redacted]
   Modified by: [Redacted]
                [Redacted]

   Defines the AST we parse to
-}
module Compile.Types.AST where

import Text.ParserCombinators.Parsec.Pos (SourcePos)
import Text.PrettyPrint.HughesPJ
import Control.Monad.Free.Class
import qualified Control.Monad.Free as M
import qualified Control.MonadOr.Free as MP
import Control.Applicative
import Data.Foldable
import Data.Traversable
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Comonad.Trans.Env

import Compile.Types.Ops


type Ident = String

data Value id = LVal (LValue id)
              | Int Integer
              | Bool Bool
              | Effect
              deriving (Eq, Show)

type AST id stmt = [TopLevelDecl id stmt]

data TopLevelDecl id stmt = FnDef (VarDecl Ident) [VarDecl id] stmt
                          | FnDecl (VarDecl Ident) [VarDecl id]
                          | TypeDef (C0Type id) id SourcePos
                          deriving (Eq, Show)

stripSourcePos :: AST id (SStmt id)
               -> AST id (Stmt id (Expr (Value id)) (Expr (Value id)))
stripSourcePos = fmap stripTopLevel
  where
    stripTopLevel (FnDef v p s) = FnDef v p (stripSStmt s)
    stripTopLevel (FnDecl v params) = FnDecl v params
    stripTopLevel (TypeDef t id pos) = TypeDef t id pos

data VarDecl id = VarDecl (C0Type id) id SourcePos
                deriving (Eq, Show)

data C0Type id = IntType
               | BoolType
               | VoidType
               | TypeSynonym id
               | FnType [C0Type id] (C0Type id)
               deriving (Eq, Show, Ord)


-- MP.Free, the Free MonadPlus, allows Stmts to be either
-- a return Expr, a Control built from Stmts, or a list of Stmts.
-- MP.Pure :: (Expr id, SourcePos) -> Stmt id
-- MP.Free :: Control id (Stmt id) -> Stmt id
-- MP.Plus :: [Stmt id] -> Stmt id
data Ctrl id expr block = Declare (VarDecl id) block
                        | Assign (LValue id) expr
                        | If expr block block
                        | While expr block
                        | Eval expr
                        | Assert expr
                        deriving (Eq, Show, Functor)

type Stmt id expr ret = MP.Free (Ctrl id expr) ret
                                      
type SCtrl id expr = EnvT SourcePos (Ctrl id expr)
type SStmt id = MP.Free (SCtrl id (SExpr id)) (Env SourcePos (SExpr id))

stripSStmt :: SStmt id -> Stmt id (Expr (Value id)) (Expr (Value id))
stripSStmt (MP.Pure e) = MP.Pure $ stripSExpr $ snd $ runEnv e
stripSStmt (MP.Plus ss) = MP.Plus $ map stripSStmt ss
stripSStmt (MP.Free s) =
  case snd $ runEnvT s of
    Declare v b -> wrap $ Declare v (stripSStmt b)
    Assign v e -> wrap $ Assign v $ stripSExpr e
    If e s1 s2 -> wrap $ If (stripSExpr e) (stripSStmt s1) (stripSStmt s2)
    While e s -> wrap $ While (stripSExpr e) (stripSStmt s)
    Eval e -> wrap $ Eval (stripSExpr e)
    Assert e -> wrap $ Assert (stripSExpr e)


infixr 5 =:
(=:) :: LValue id -> expr -> Stmt id expr ret
(=:) v e = wrap $ Assign v e

hasBlock :: SStmt id -> Bool
hasBlock (MP.Pure _) = False
hasBlock (MP.Plus _) = True
hasBlock (MP.Free s) = case snd $ runEnvT s of
  (Declare _ _) -> True
  (Assign _ _) -> False
  (If _ thn els) -> hasBlock thn || hasBlock els
  (While _ blk) -> hasBlock blk
  (Eval _) -> False

instance Traversable (Ctrl id expr) where
  sequenceA (Declare v b) = Declare v <$> b
  sequenceA (Assign v e) = pure $ Assign v e
  sequenceA (If cond thn els) = If cond <$> thn <*> els
  sequenceA (While cond block) = While cond <$> block
  sequenceA (Eval e) = pure $ Eval e

instance Foldable (Ctrl id expr) where
  foldMap = foldMapDefault

data LValue id = Var id
               deriving (Eq, Show, Ord)


-- M.Free, the Free Monad, allows Expr's to be either an LValue
-- or a Term built from Expr's.
-- M.Pure :: LValue id -> Expr id
-- M.Free :: Term (Expr id) -> Expr id
type Expr id = M.Free Term id

data Term expr = BinOp Op expr expr
               | UnOp Op expr
               | Cond expr expr expr
               | Call Ident [expr]
               deriving (Eq, Show, Functor)
                        
type STerm = EnvT SourcePos Term
type SExpr id = M.Free STerm (Env SourcePos (Value id))

instance Traversable Term where
  sequenceA (BinOp op e1 e2) = BinOp op <$> e1 <*> e2
  sequenceA (UnOp op e) = UnOp op <$> e
  sequenceA (Cond e1 e2 e3) = Cond <$> e1 <*> e2 <*> e3
  sequenceA (Call f es) = Call f <$> sequenceA es

instance Foldable Term where
  foldMap = foldMapDefault


stripSExpr :: SExpr id -> Expr (Value id)
stripSExpr = fmap (snd . runEnv) . M.hoistFree (snd . runEnvT)
  
                   
type AsnOp = Maybe Op


instance Eq a => Eq (Env SourcePos a) where
  a1 == a2 = (snd $ runEnv a1) == (snd $ runEnv a2)
  
instance Ord a => Ord (Env SourcePos a) where
  compare a1 a2 = compare (snd $ runEnv a1) (snd $ runEnv a2)

instance Eq a => Eq (SourcePos, a) where
  (_, a1) == (_, a2) = a1 == a2
  
instance Ord a => Ord (SourcePos, a) where
  compare (_, a1) (_, a2) = compare a1 a2

used :: Ord id => SExpr id -> Set (SourcePos, LValue id)
used (M.Pure v) =
  case runEnv v of
    (pos, LVal v) -> Set.singleton (pos, v)
    _ -> Set.empty
used (M.Free e) =
  case snd $ runEnvT e of
    BinOp _ e1 e2 -> Set.union (used e1) (used e2)
    UnOp _ e -> used e
    Cond e1 e2 e3 -> Set.unions [used e1, used e2, used e3]
    Call _ es -> Set.unions $ map used es

defined :: Ord id => Set (LValue id) -> SStmt id -> Set (SourcePos, LValue id)
defined ctx (MP.Pure e) = Set.map (fst (runEnv e),) ctx
defined ctx (MP.Plus ss) = Set.unions $ map (defined ctx) ss
defined ctx (MP.Free s) =
  case runEnvT s of
    (_, Declare (VarDecl t id _) s') -> let
      ctx' = Set.insert (Var id) ctx in
      Set.filter ((/= Var id) . snd) $ defined ctx' s'
    (pos, Assign v e) -> Set.singleton (pos, v)
    (_, If e s1 s2) -> Set.intersection (defined ctx s1) (defined ctx s2)
    (_, While e s) -> Set.empty
    (_, Eval _) -> Set.empty
    (_, Assert _) -> Set.empty

live :: Ord id => Set (LValue id) -> SStmt id -> Set (SourcePos, LValue id)
live ctx (MP.Pure e) = used $ snd $ runEnv e
live ctx (MP.Plus []) = Set.empty
live ctx (MP.Plus (s : ss)) = Set.union (live ctx s) $
  Set.filter (`Set.notMember` defined ctx s) $ live ctx (MP.Plus ss)
live ctx (MP.Free s) =
  case snd $ runEnvT s of
    Declare (VarDecl _ id _) s' -> let
      ctx' = Set.insert (Var id) ctx in
      Set.filter ((/= Var id) . snd) $ live ctx' s'
    Assign v e -> used e
    If e s1 s2 -> Set.unions [used e, live ctx s1, live ctx s2]
    While e s -> Set.union (used e) (live ctx s)
    Eval e -> used e
    Assert e -> used e


-- Note to the student: You will probably want to write a new pretty printer
-- using the module Text.PrettyPrint.HughesPJ from the pretty package
-- This is a quick and dirty pretty printer.
-- Once that is written, you may find it helpful for debugging to switch
-- back to the deriving Show instances.

renderC0 :: AST Ident (SStmt Ident) -> String
renderC0 = render . ppAST

ppAST :: AST Ident (SStmt Ident) -> Doc
ppAST = vcat . map ppTopLevelDecl

ppTopLevelDecl :: TopLevelDecl Ident (SStmt Ident) -> Doc
ppTopLevelDecl (FnDef decl params stmts) =
  ppVarDecl decl <+> (parens . hsep . punctuate comma . map ppVarDecl) params <+> lbrace
                 $+$ nest 4 (ppStmt stmts)
                 $+$ rbrace
ppTopLevelDecl (FnDecl decl params) =
  ppVarDecl decl <+> (parens . hsep . punctuate comma . map ppVarDecl) params <> semi
ppTopLevelDecl (TypeDef t id _) = text "typedef" <+> ppType t <+> text id <> semi

ppVarDecl :: VarDecl Ident -> Doc
ppVarDecl (VarDecl typ ident _) = ppType typ <+> text ident

ppType :: C0Type Ident -> Doc
ppType IntType = text "int"
ppType BoolType = text "bool"
ppType VoidType = text "void"
ppType (TypeSynonym id) = text id
ppType (FnType params out) =
  parens (hsep $ punctuate comma $ map ppType params)
  <+> text "->" <+>
  ppType out

ppStmt :: SStmt Ident -> Doc
ppStmt = MP.iter ppCtrl (\s -> lbrace $+$ nest 4 (vcat s) $+$ rbrace) 
         . fmap (\e -> text "return" <+> ppExpr (snd $ runEnv e) <> semi)

ppCtrl :: SCtrl Ident (SExpr Ident) Doc -> Doc
ppCtrl (snd . runEnvT -> Eval e) = ppExpr e <> semi
ppCtrl (snd . runEnvT -> Assert e) = text "assert" <>
                                     parens (ppExpr e)
                                     <> semi
ppCtrl (snd . runEnvT -> Declare decl s) = ppVarDecl decl <> semi $+$ s
ppCtrl (snd . runEnvT -> Assign val e) =
  ppLValue val <+> char '=' <+> ppExpr e <> semi
ppCtrl (snd . runEnvT -> If e thn els) =
  text "if" <+> parens (ppExpr e) <+> lbrace
            $+$ nest 4 thn
            $+$ rbrace
  $+$ text "else" <+> lbrace
                  $+$ nest 4 els
                  $+$ rbrace
ppCtrl (snd . runEnvT -> While e b) =
  text "while" <+> parens (ppExpr e) <+> lbrace
               $+$ nest 4 b
               $+$ rbrace

ppLValue :: LValue Ident -> Doc
ppLValue (Var ident) = text ident

ppExpr :: SExpr Ident -> Doc
ppExpr = M.iter (ppTerm . snd . runEnvT)
         . fmap (ppValue . snd . runEnv)

ppTerm :: Term Doc -> Doc
ppTerm (BinOp o e1 e2) = parens (e1 <+> ppOp o <+> e2)
ppTerm (UnOp o e) = parens (ppOp o <> e)
ppTerm (Cond e1 e2 e3) = parens (e1 <+> char '?' <+> e2 <+> char ':' <+> e3)
ppTerm (Call f es) = text f <> parens (hsep $ punctuate comma es)

ppValue :: Value Ident -> Doc
ppValue (LVal v) = ppLValue v
ppValue (Int i) = integer i
ppValue (Bool True) = text "true"
ppValue (Bool False) = text "false"
ppValue Effect = text ""

ppOp :: Op -> Doc
ppOp = text . show
