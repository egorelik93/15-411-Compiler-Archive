module Compile.Types.Grammar where

-- Concrete Syntax Tree

import Text.Parsec.Pos (SourcePos)


type Ident = String


type Program = [GDecl]

data GDecl = FDecl C0Type Ident ParamList SourcePos
           | FDef C0Type Ident ParamList Block SourcePos
           | TypeDef C0Type Ident SourcePos
           | SDecl Ident SourcePos
           | SDef Ident FieldList SourcePos
           deriving (Show, Eq)

data Param = Param C0Type Ident SourcePos
           deriving (Show, Eq)
type ParamList = [Param]

data Field = Field C0Type Ident deriving (Show, Eq)
type FieldList = [Field]

data C0Type = IntType
            | BoolType
            | VoidType
            | DefType Ident
            | PointerTo C0Type
            | ArrayOf C0Type
            | Struct Ident
            deriving (Show, Eq)

newtype Block = Block Stmts deriving (Show, Eq)
type Stmts = [Stmt]

data Stmt = Simp Simp
          | Control Control
          | Multi Block
          deriving (Show, Eq)

data Decl = UnInit C0Type Ident
          | Init C0Type Ident Exp
          deriving (Show, Eq)

data Simp = AsnLValue LValue AsnOp Exp SourcePos
          | PostOp LValue PostOp SourcePos
          | Decl Decl SourcePos
          | Exp Exp SourcePos
          deriving (Show, Eq)

type SimpOpt = Maybe Simp

data LValue = Var Ident
            | VarField LValue Ident SourcePos
            | VarPField LValue Ident SourcePos
            | Pointer LValue
            | Array LValue Exp
            | ParenLValue LValue
            deriving (Show, Eq)

type ElseOpt = Maybe Stmt

data Control = If Exp Stmt ElseOpt SourcePos
             | While Exp Stmt SourcePos
             | For (SimpOpt, Exp, SimpOpt) Stmt SourcePos
             | Continue SourcePos
             | Break SourcePos
             | Return (Maybe Exp) SourcePos
             | Assert Exp SourcePos   
             deriving (Show, Eq)

type ArgList = [Exp]

data Exp = ParenExp Exp SourcePos
         | Int IntConst SourcePos
         | C0True SourcePos
         | C0False SourcePos
         | Val Ident SourcePos
         | UnOp UnOp Exp SourcePos
         | BinOp BinOp Exp Exp SourcePos
         | Cond Exp Exp Exp SourcePos
         | Apply Ident ArgList SourcePos
         | ValField Exp Ident SourcePos
         | ValPField Exp Ident SourcePos
         | Alloc C0Type SourcePos
         | DeRef Exp SourcePos
         | NULL SourcePos
         | AllocArray (C0Type, Exp) SourcePos
         | Index Exp Exp SourcePos
         deriving (Show, Eq)

data IntConst = Dec Integer
              | Hex Integer
              deriving (Show, Eq)

data AsnOp = Asn
           | PAsn
           | MAsn
           | TAsn
           | DAsn
           | ModAsn
           | ANDAsn
           | XORAsn
           | ORAsn
           | SLAsn
           | SRAsn
           deriving (Show, Eq)

data BinOp = Plus
           | Minus
           | Times
           | Divide
           | Mod
           | Lt
           | LtE
           | Gt
           | GtE
           | Eq
           | NEq
           | And
           | Or
           | AND
           | XOR
           | OR
           | SL
           | SR
           deriving (Show, Eq)

data UnOp = Bang
          | Comp
          | Neg
          deriving (Show, Eq)

data PostOp = PP
            | MM
            deriving (Show, Eq)
