{- L1 Compiler
   Author: *[Redacted]
   Modified by: [Redacted]

   Abstract Assembly operations
-}
module Compile.Types.Ops where

data Op = Mul
        | Add
        | Sub
        | Div
        | Neg
        | Mod
        | Not
        | Comp
        | Lt
        | LtE
        | Gt
        | GtE
        | Eq
        | NEq
        | AND
        | XOR
        | OR
        | SL
        | SR
        | Nop
        deriving Eq

instance Show Op where
  show Mul = "*"
  show Add = "+"
  show Sub = "-"
  show Div = "/"
  show Neg = "-"
  show Mod = "%"
  show Not = "!"
  show Comp = "~"
  show Lt = "<"
  show LtE = "<="
  show Gt = ">"
  show GtE = ">="
  show Eq = "=="
  show NEq = "!="
  show AND = "&"
  show XOR = "^"
  show OR = "|"
  show SL = "<<"
  show SR = ">>"
  show Nop = "[nop]"

data COp = Ret deriving (Eq, Show)
