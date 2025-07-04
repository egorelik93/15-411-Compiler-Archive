{- L1 Compiler
   Author: *[Redacted]
   Modified by: [Redacted]

   This is a modified version of parsec
-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Text.Parsec
-- Copyright   :  (c) Daan Leijen 1999-2001, (c) Paolo Martini 2007
-- License     :  BSD-style (see the LICENSE file)
-- 
-- Maintainer  :  derek.a.elkins@gmail.com
-- Stability   :  provisional
-- Portability :  portable
-- 
-----------------------------------------------------------------------------

module Text.Parsec
    ( module Text.Parsec.Prim
    , module Text.Parsec.Char
    , module Text.Parsec.Combinator
    , ParseError
    , errorPos
    , SourcePos
    , SourceName, Line, Column
    , sourceName, sourceLine, sourceColumn
    , incSourceLine, incSourceColumn
    , setSourceLine, setSourceColumn, setSourceName
    ) where

import Text.Parsec.Pos
import Text.Parsec.Error
import Text.Parsec.Prim
import Text.Parsec.Char
import Text.Parsec.Combinator
import Text.Parsec.String          ()
import Text.Parsec.ByteString      ()
import Text.Parsec.ByteString.Lazy ()
