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
import Control.Comonad.Trans.Env

import Compile.Types.Ops


type Ident = String

data Value id = LVal (LValue id)
              | Int Integer
              | Bool Bool
              deriving (Eq, Show)

type AST id stmt = [TopLevelDecl id stmt]

data TopLevelDecl id stmt = FnDef (VarDecl id) [VarDecl id] stmt
                     deriving (Eq, Show)

data VarDecl id = VarDecl (C0Type id) id SourcePos
                deriving (Eq, Show)

data C0Type id = IntType
               | BoolType
               deriving (Eq, Show)


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
                        deriving (Eq, Show, Functor)

type Stmt id expr ret = MP.Free (Ctrl id expr) ret
                                      
type SCtrl id expr = EnvT SourcePos (Ctrl id expr)
type SStmt id = MP.Free (SCtrl id (SExpr id)) (Env SourcePos (SExpr id))


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
               deriving (Eq, Show)


-- M.Free, the Free Monad, allows Expr's to be either an LValue
-- or a Term built from Expr's.
-- M.Pure :: LValue id -> Expr id
-- M.Free :: Term (Expr id) -> Expr id
type Expr id = M.Free Term id

data Term expr = BinOp Op expr expr
               | UnOp Op expr
               | Cond expr expr expr
               deriving (Eq, Show, Functor)
                        
type STerm = EnvT SourcePos Term
type SExpr id = M.Free STerm (Env SourcePos (Value id))

instance Traversable Term where
  sequenceA (BinOp op e1 e2) = BinOp op <$> e1 <*> e2
  sequenceA (UnOp op e) = UnOp op <$> e
  sequenceA (Cond e1 e2 e3) = Cond <$> e1 <*> e2 <*> e3

instance Foldable Term where
  foldMap = foldMapDefault
  
                   
type AsnOp = Maybe Op


-- Note to the student: You will probably want to write a new pretty printer
-- using the module Text.PrettyPrint.HughesPJ from the pretty package
-- This is a quick and dirty pretty printer.
-- Once that is written, you may find it helpful for debugging to switch
-- back to the deriving Show instances.

renderC0 :: AST Ident (SStmt Ident) -> String
renderC0 = render . ppAST

ppAST :: AST Ident (SStmt Ident) -> Doc
ppAST = hsep . map ppTopLevelDecl

ppTopLevelDecl :: TopLevelDecl Ident (SStmt Ident) -> Doc
ppTopLevelDecl (FnDef decl params stmts) =
  ppVarDecl decl <+> (parens . hsep . punctuate comma . map ppVarDecl) params <+> lbrace
                 $+$ nest 4 (ppStmt stmts)
                 $+$ rbrace

ppVarDecl :: VarDecl Ident -> Doc
ppVarDecl (VarDecl typ ident _) = ppType typ <+> text ident

ppType :: C0Type Ident -> Doc
ppType IntType = text "int"
ppType BoolType = text "bool"

ppStmt :: SStmt Ident -> Doc
ppStmt = MP.iter ppCtrl (\s -> lbrace $+$ nest 4 (vcat s) $+$ rbrace) 
         . fmap (\e -> text "return" <+> ppExpr (snd $ runEnv e) <> semi)

ppCtrl :: SCtrl Ident (SExpr Ident) Doc -> Doc
ppCtrl (snd . runEnvT -> Eval e) = ppExpr e <> semi
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

ppValue :: Value Ident -> Doc
ppValue (LVal v) = ppLValue v
ppValue (Int i) = integer i
ppValue (Bool True) = text "true"
ppValue (Bool False) = text "false"

ppOp :: Op -> Doc
ppOp = text . show
