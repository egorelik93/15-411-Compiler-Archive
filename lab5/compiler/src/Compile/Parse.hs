{- L1 Compiler
   Author: *[Redacted]
   Modified by: [Redacted]
                [Redacted]

   The start of a parser.

   Note that this uses a modified version of Parsec. We do 
   not advise replacing this modified version with a stock one.
-}
module Compile.Parse where

import Control.Monad.Error
import Data.ByteString as BS
import Data.Char
import Data.Functor((<$>))
import Control.Applicative((<*>))
import Compile.Types

import LiftIOE

import Text.ParserCombinators.Parsec hiding (try)
import Control.Monad.Identity                 -- For our custom Language Definition
import Text.Parsec hiding (parse)             -- Parser Combinators
import Text.Parsec.Expr                       -- Expression Parser Generator
import Text.Parsec.Token (GenLanguageDef(..)) -- Language Definition Structure
import qualified Text.Parsec.Token as Tok
import Text.Parsec.Combinator
import Text.Parsec.ByteString
import Text.Parsec.Char

parseAST :: FilePath -> ErrorT String IO AST
parseAST file = do
  code <- liftIOE $ BS.readFile file
  case parse astParser file code of
    Left e  -> throwError (show e)
    Right a -> return a

type C0Parser = Parsec ByteString ()

astParser :: C0Parser AST
astParser = do
  whiteSpace
  reserved "int"
  reserved "main"
  parens $ return ()
  block <- braces (do
                      pos   <- getPosition
                      stmts <- many stmt
                      return $ [FnDef (VarDecl IntType "main" pos) [] stmts]
                      <?> "block"
                  )
  whiteSpace
  eof
  return block
  

varDecl :: C0Parser VarDecl
varDecl = do
   pos   <- getPosition
   reserved "int"
   ident <- identifier
   return $ VarDecl IntType ident pos
   <?> "declaration"

lvalue :: C0Parser LValue
lvalue = parens lvalue <|>
         do
           dest <- identifier
           return $ Var dest

stmt :: C0Parser Stmt
stmt =
  (do
      decl <- varDecl
      e <- optionMaybe $ do
        reservedOp "="
        expr
      semi
      return $ Declare decl e
  )
  <|>
  (do
   pos  <- getPosition
   dest <- lvalue
   op   <- asnOp
   e    <- expr
   semi
   return $ Assign dest op e pos)
   <|>
   (do pos <- getPosition
       reserved "return"
       e <- expr
       semi
       return $ Return e pos)
   <?> "statement"

asnOp :: C0Parser (Maybe Op)
asnOp = do
   op <- operator
   return $ case op of
               "+="  -> Just Add
               "*="  -> Just Mul
               "-="  -> Just Sub
               "/="  -> Just Div
               "%="  -> Just Mod
               "="   -> Nothing
               x     -> fail $ "Nonexistent assignment operator: " ++ x
   <?> "assignment operator"


expr :: C0Parser Expr
expr = buildExpressionParser opTable term <?> "expr"

readNumBase :: Int -> String -> Integer
readNumBase b n = toInteger $ Prelude.foldl (\ n d -> n * b + digitToInt d) 0 n

decnum :: C0Parser Integer
decnum = Tok.lexeme c0Tokens $ do
  n <- readNumBase 10 <$> ((:) <$> oneOf ['1' .. '9'] <*> many digit
                           <|> string "0")
  if (n > 2 ^ 31 || n < 0) then fail $ "Integer " ++ show n ++ " out of range"
    else return n
              
hexnum :: C0Parser Integer
hexnum = Tok.lexeme c0Tokens $ do
  n <- readNumBase 16 <$> (char '0' >> oneOf "xX" >> many1 hexDigit)
  if (n > 0xffffffff || n < 0x00000000)
    then fail $ "Integer " ++ show n ++ " out of range"
    else return n

num :: C0Parser Integer
num = try hexnum
      <|> decnum

term :: C0Parser Expr
term = do
   parens expr
   <|>
   (do p <- getPosition
       i <- identifier
       return $ Val (Var i) p)
   <|>
   (do p <- getPosition
       n <- num
       return $ Int n p)
   <?> "term"

c0Def :: GenLanguageDef ByteString () Identity
c0Def = LanguageDef
   {commentStart    = string "/*",
    commentStartStr = "/*",
    commentEnd      = string "*/",
    commentEndStr   = "*/",
    commentLine     = string "#" <|> string "//",
    nestedComments  = True,
    identStart      = letter <|> char '_',
    identLetter     = alphaNum <|> char '_',
    opStart         = oneOf "=+-*/%&^|<>!~",
    opLetter        = oneOf "=&|<>",
    reservedNames   = ["int", "char", "string", "void", "while", "for", "if",
                       "return", "break", "continue", "NULL", "alloc",
                       "alloc_array", "typedef", "struct", "else", "assert",
                       "true", "false", "bool"],
    reservedOpNames = ["+",  "*",  "-",  "/",  "%", "?", ":", "->", "."],
    caseSensitive   = True}

c0Tokens :: Tok.GenTokenParser ByteString () Identity
c0Tokens = Tok.makeTokenParser c0Def

reserved   :: String -> C0Parser ()
reserved   = Tok.reserved   c0Tokens
comma      :: C0Parser ()
comma      = do _ <- Tok.comma c0Tokens; return ()
semi       :: C0Parser ()
semi       = do _ <- Tok.semi c0Tokens; return ()
identifier :: C0Parser String
identifier = Tok.identifier c0Tokens
operator   :: C0Parser String
operator   = Tok.operator   c0Tokens
braces     :: C0Parser a -> C0Parser a
braces     = Tok.braces     c0Tokens
parens     :: C0Parser a -> C0Parser a
parens     = Tok.parens     c0Tokens
reservedOp :: String -> C0Parser ()
reservedOp = Tok.reservedOp c0Tokens
natural    :: C0Parser Integer
natural    = Tok.natural    c0Tokens
whiteSpace :: C0Parser ()
whiteSpace = Tok.whiteSpace c0Tokens
commaSep   :: C0Parser a -> C0Parser [a]
commaSep   = Tok.commaSep c0Tokens
semiSep    :: C0Parser a -> C0Parser [a]
semiSep    = Tok.semiSep c0Tokens
brackets   :: C0Parser a -> C0Parser a
brackets   = Tok.brackets c0Tokens

opTable :: [[Operator ByteString () Identity Expr]]
opTable = [[Prefix $ do
               pos <- getPosition
               (try (reservedOp "--" >> error "-- is a reserved operator")
                <|>
                (do reservedOp "-"
                    return (\x -> UnOp Neg x pos))
                 ),
            Postfix $ do
              reservedOp "--"
              error "-- is a reserved operator"
           ],
           [binary "*"   (BinOp Mul)  AssocLeft,
            binary "/"   (BinOp Div)  AssocLeft,
            binary "%"   (BinOp Mod)  AssocLeft],
           [binary "+"   (BinOp Add)  AssocLeft,
            binary "-"   (BinOp Sub)  AssocLeft]]
{-
We used a few helper functions which are in the Parsec documentation of Text.Parsec.Expr, located at \url{http://hackage.haskell.org/packages/archive/parsec/3.1.0/doc/html/Text-Parsec-Expr.html} The functions ``binary'', ``prefix'', and ``postfix'' were taken from there and are not my work, however they are used because rewriting them would look much the same, and they do not provide any core functionality, just make my code easier to read. Type signatures and location annotations were added by me.
-}
binary :: String -> (a -> a -> SourcePos -> a) -> Assoc -> Operator ByteString () Identity a
binary  name f = Infix $ do pos <- getPosition
                            reservedOp name
                            return $ \x y -> f x y pos
prefix :: String -> (a -> SourcePos -> a) -> Operator ByteString () Identity a
prefix  name f = Prefix $ do pos <- getPosition
                             reservedOp name
                             return $ \x -> f x pos
