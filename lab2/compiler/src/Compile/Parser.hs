module Compile.Parser where

import Prelude hiding (exp)
import Control.Applicative ((<$>), (<*>), (*>), (<*), (<$))
import Text.Parsec
import Text.Parsec.Expr
import Text.Parsec.Pos
import Text.Parsec.ByteString
import Control.Monad.Identity
import Control.Monad.Error
import Data.ByteString as BS

import LiftIOE

import Compile.Types.Grammar
import Compile.Lexer


type C0Parser = Parsec ByteString ()

parseProgram :: FilePath -> ErrorT String IO Program
parseProgram file = do
  code <- liftIOE $ BS.readFile file
  case parse c0 file code of
    Left e -> throwError (show e)
    Right a -> return a

-- Utility for adding source positions
withPos :: Parsec s () (SourcePos -> e) -> Parsec s () e
withPos p = do
  pos <- getPosition
  content <- p
  return $ content pos


-- Operator definitions

binary :: String -> (a -> a -> SourcePos -> a) -> Assoc -> Operator ByteString () Identity a
binary syntax ast assoc =
  Infix (do
            pos <- getPosition
            op syntax
            return $ \e1 e2 -> ast e1 e2 pos
        ) assoc

prefix :: String -> (a -> SourcePos -> a) -> Operator ByteString () Identity a
prefix syntax ast = Prefix $ do
  pos <- getPosition
  op syntax
  return $ \e -> ast e pos

postfix :: String -> (a -> SourcePos -> a) -> Operator ByteString () Identity a
postfix syntax ast = Postfix $ do
  pos <- getPosition
  op syntax
  return $ \e -> ast e pos

-- The ternary conditional operator will be parsed by
-- treating the entire "? exp :" portion as an operator
ternaryCondOp :: Operator ByteString () Identity Exp
ternaryCondOp =
  Infix (do
            pos <- getPosition
            op "?"
            e2 <- exp
            op ":"
            return $ \e1 e3 -> Cond e1 e2 e3 pos
        ) AssocRight

-- Array indexing is treated as a postfix operator,
-- with the index as the entire operator
indexOp :: forall u. Parsec ByteString () (Exp -> Exp)
indexOp = do
  pos <- getPosition
  e2 <- inBrackets exp
  return $ \e1 -> Index e1 e2 pos

-- Field operations . and ->, which produce exp and take and exp
-- as the first argument, but use an identifier as the second
fieldOp :: String -> (e -> Ident -> SourcePos -> e) -> Parsec ByteString () (e -> e)
fieldOp syntax ast = do
  pos <- getPosition
  op syntax
  i <- ident
  return $ \e -> ast e i pos

-- Precedence Table
-- Not all operators take expressions as arguments,
-- so we need to parse those separately from the operator table

operators = [
  [ Postfix indexOp
  , Postfix $ fieldOp "->" ValPField
  , Postfix $ fieldOp "." ValField
  ],
  [ prefix "!" $ UnOp Bang
  , prefix "~" $ UnOp Comp
  , Prefix $ do
    pos <- getPosition
    try (do
            op "--"
            error "-- is not a prefix operator"
        )
      <|> op "-"
    return $ \e -> UnOp Neg e pos
  ],
  [ binary "*" (BinOp Times) AssocLeft
  , binary "/" (BinOp Divide) AssocLeft
  , binary "%" (BinOp Mod) AssocLeft
  ],
  [ binary "+" (BinOp Plus) AssocLeft
  , binary "-" (BinOp Minus) AssocLeft
  ],
  [ binary "<<" (BinOp SL) AssocLeft
  , binary ">>" (BinOp SR) AssocLeft
  ],
  [ binary "<=" (BinOp LtE) AssocLeft
  , binary ">=" (BinOp GtE) AssocLeft
  , binary "<" (BinOp Lt) AssocLeft
  , binary ">" (BinOp Gt) AssocLeft
  ],
  [ binary "==" (BinOp Eq) AssocLeft
  , binary "!=" (BinOp NEq) AssocLeft
  ],
  [binary "&" (BinOp AND) AssocLeft],
  [binary "^" (BinOp XOR) AssocLeft],
  [binary "|" (BinOp OR) AssocLeft],
  [binary "&&" (BinOp And) AssocLeft],
  [binary "||" (BinOp Or) AssocLeft],
  [ternaryCondOp]
  ]



c0 = parseAll program

program = many gdecl

gdecl = choice [
  withPos typedef,
  try $ withPos sdef,
  withPos sdecl,
  try $ withPos fdef,
  withPos fdecl
  ] <?> "top-level declaration"

fdecl = FDecl <$> c0type <*> ident <*> paramList <* semi
        <?> "function declaration"

fdef = FDef <$> c0type <*> ident <*> paramList <*> block
       <?> "function definition"

param = withPos (Param <$> c0type <*> ident) <?> "parameter"
paramList = inParens (commaSep param) <?> "parameter list"

typedef = TypeDef <$> (keyword "typedef" *> c0type) <*> ident <* semi

sdecl = SDecl <$> (keyword "struct" *> ident) <* semi
sdef = SDef <$> (keyword "struct" *> ident) <*> inBraces fieldList <* semi

field = Field <$> c0type <*> ident <* semi
fieldList = many field

c0type = (
  buildExpressionParser
  [[ Postfix $ PointerTo <$ op "*"
   , Postfix $ ArrayOf <$ inBrackets (return ())
  ]]
  $ choice [
    IntType <$ symbol "int",
    BoolType <$ symbol "bool",
    Struct <$> (keyword "struct" *> ident),
    DefType <$> ident
    ]
  ) <?> "type"

block = Block <$> inBraces stmts <?> "block"
stmts = many stmt

stmt = choice [
  Multi <$> block,
  Control <$> control,
  Simp <$> simp <* semi
  ] <?> "statement"

decl = choice [
  try $ Init <$> c0type <*> ident <*> (op "=" *> exp),
  UnInit <$> c0type <*> ident
  ] <?> "variable declaration"

simp = choice [
  try $ withPos $ AsnLValue <$> lvalue <*> asnop <*> exp,
  try $ withPos $ Decl <$> decl,
  try $ withPos $ PostOp <$> lvalue <*> postop,
  withPos $ Exp <$> exp
  ]

simpopt = optionMaybe simp

lvalue = buildExpressionParser
  [[ Prefix $ Pointer <$ op "*"
   , Postfix $ fieldOp "." VarField
   , Postfix $ fieldOp "->" VarPField
   , Postfix $ flip Array <$> inBrackets exp
   ]]
  $ choice [
    Var <$> ident,
    ParenLValue <$> inParens lvalue
    ]

elseopt = optionMaybe $ keyword "else" *> stmt

control = choice [
  withPos $ If <$> (keyword "if" *> inParens exp) <*> stmt <*> elseopt,
  withPos $ While <$> (keyword "while" *> inParens exp) <*> stmt,
  withPos $ For <$> (keyword "for" *>
                     inParens ((,,) <$>
                               simpopt <* semi
                               <*> exp <* semi
                               <*> simpopt
                              )
                    ) <*> stmt,
  withPos $ Continue <$ keyword "continue" <* semi,
  withPos $ Break <$ keyword "break" <* semi,
  withPos $ Return <$> (keyword "return" *> exp) <* semi
  ]


argList = inParens (commaSep exp)

exp = buildExpressionParser operators $ withPos $ choice [
  ParenExp <$> inParens exp <?> "subexpression",
  Int <$> intconst,
  C0True <$ keyword "true",
  C0False <$ keyword "false",
  NULL <$ keyword "NULL",
  try $ DeRef <$> (op "*" *> exp),
  Alloc <$> (keyword "alloc" *> inParens c0type) <?> "",
  AllocArray <$> (keyword "alloc_array" *>
                  inParens ((,) <$> c0type <* comma <*> exp)) <?> "", 
  try (Apply <$> ident <*> argList) <?> "function call",
  Val <$> ident <?> "variable"
  ]
      
intconst = num <?> "integer"

asnop = choice [
  PAsn <$ op "+=",
  MAsn <$ op "-=",
  TAsn <$ op "*=",
  DAsn <$ op "/=",
  ModAsn <$ op "%=",
  ANDAsn <$ op "&=",
  XORAsn <$ op "^=",
  ORAsn <$ op "|=",
  SLAsn <$ op "<<=",
  SRAsn <$ op ">>=",
  Asn <$ op "="
  ] <?> "assignment"

postop = choice [
  PP <$ op "++",
  MM <$ op "--"
  ]
