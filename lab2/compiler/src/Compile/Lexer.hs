module Compile.Lexer (lexer,
                      ident,
                      num,
                      op,
                      keyword,
                      symbol,
                      inParens,
                      inBrackets,
                      inBraces,
                      comma,
                      commaSep,
                      semi,
                      parseAll)
       where

import Control.Applicative ((<$>), (<*>), empty)
import Data.Char (digitToInt)
import Text.Parsec
import Text.Parsec.Char
import Text.Parsec.Token (GenLanguageDef(..))
import Control.Monad.Identity
import Data.ByteString (ByteString)
import qualified Text.Parsec.Token as T

import Compile.Types.Grammar


c0Def :: GenLanguageDef ByteString u Identity
c0Def = LanguageDef {
  commentStart = string "/*",
  commentStartStr = "/*",
  commentEnd = string "*/",
  commentEndStr = "*/",
  commentLine = string "//",
  nestedComments = True,
  identStart = letter <|> char '_',
  identLetter = alphaNum <|> char '_',
  opStart = oneOf "=+-*/%&^|<>!~",
  opLetter = oneOf "=&|<>",
  reservedNames = ["struct", "typedef", "if", "else", "while", "for",
                   "continue", "break", "return", "assert", "true", "false",
                   "NULL", "alloc", "alloc_array", "int", "bool", "void",
                   "char", "string"
                   --, "main"
                  ],
  reservedOpNames = ["!", "~", "-", "+", "*", "/", "%", "<<", ">>",
                     "<", ">", ">=", "<=", "==", "!=", "&", "^", "|",
                     "&&", "||",
                     "=", "+=", "-=", "*=", "/=", "%=", "<<=", ">>=", "&=",
                     "|=", "^=",
                     "->", ".", "--", "++", "(", "|", ")", "[", "]", ";",
                     ":", "?"],
  caseSensitive = True
  }


lexer = T.makeTokenParser c0Def

ident = T.identifier lexer

readNumBase :: Int -> String -> Integer
readNumBase b n = toInteger $ foldl (\ n d -> n * b + digitToInt d) 0 n

decnum :: Parsec ByteString u Integer
decnum = T.lexeme lexer $
         readNumBase 10 <$> ((:) <$> oneOf ['1' .. '9'] <*> many digit
                             <|> string "0")
         
hexnum :: Parsec ByteString u Integer
hexnum = T.lexeme lexer $ readNumBase 16 <$>
         (char '0' >> oneOf "xX" >> many1 hexDigit)

num :: Parsec ByteString u IntConst
num = (try $ Hex <$> hexnum)
      <|> Dec <$> decnum

op = T.reservedOp lexer
keyword = T.reserved lexer
symbol = T.symbol lexer


inBraces = T.braces lexer
inParens = T.parens lexer
inBrackets = T.brackets lexer
commaSep = T.commaSep lexer
comma = T.comma lexer
semi = T.semi lexer


parseAll p = do
  T.whiteSpace lexer
  c <- p
  eof
  return c
