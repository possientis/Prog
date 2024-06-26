module  Stitch.Lex
  ( lex
  , lexM
  ) where

import Prelude hiding ( lex )

import Control.Arrow
import Control.Applicative
import Data.Functor
import Data.Maybe

import Text.Parsec.Combinator
import Text.Parsec.Char
import Text.Parsec.Prim         hiding (many, (<|>))
import Text.Parsec.Token as Parsec
import Text.Parsec.Language

import Stitch.Monad
import Stitch.Op
import Stitch.Token

type Lexer = Parsec String ()

-- | Utility
string_ :: String -> Lexer ()
string_ = void . string

---------------------------------------------------
-- | Lex some program text into a list of 'LToken's, aborting upon failure
lexM :: String -> StitchE [LToken]
lexM = eitherToStitchE . lex

-- | Lex some program text into a list of 'LToken's
lex :: String -> Either String [LToken]
lex = left show . parse lexer ""

-- | Overall lexer
lexer :: Lexer [LToken]
lexer = (catMaybes <$> many lexer1_ws) <* eof

-- | Lex either one token or some whitespace
lexer1_ws :: Lexer (Maybe LToken)
lexer1_ws
  = (Nothing <$ whitespace)
    <|>
    (Just <$> lexer1)

-- | Lex some whitespace
whitespace :: Lexer ()
whitespace
  = choice [ void $ some space
           , block_comment
           , line_comment ]

-- | Lex a @{- ... -}@ comment (perhaps nested); consumes no input
-- if the target doesn't start with @{-@.
block_comment :: Lexer ()
block_comment = do
  try $ string_ "{-"
  comment_body

-- | Lex a block comment, without the opening "{-"
comment_body :: Lexer ()
comment_body
  = choice [ block_comment *> comment_body
           , try $ string_ "-}"
           , anyChar *> comment_body ]

-- | Lex a line comment
line_comment :: Lexer ()
line_comment = do
  try $ string_ "--"
  void $ manyTill anyChar (eof <|> void newline)

-- | Lex one token
lexer1 :: Lexer LToken
lexer1 = do
  pos <- getPosition
  L pos <$> choice 
    [ symbolic
    , word_token
    , IntTok . fromInteger <$> natural haskell 
    ]

-- | Lex one non-alphanumeric token
symbolic :: Lexer Token
symbolic = choice 
  [ LParen   <$  char '('
  , RParen   <$  char ')'
  , Lambda   <$  char '\\'
  , Dot      <$  char '.'
  , ArrowTok <$  try (string "->")
  , Colon    <$  char ':'
  , ArithOp  <$> arith_op
  , Assign   <$  char '='
  , Semi     <$  char ';' 
  ]

-- | Lex one arithmetic operator
arith_op :: Lexer UArithOp
arith_op = choice 
  [ uPlus     <$ char '+'
  , uMinus    <$ char '-'
  , uTimes    <$ char '*'
  , uDivide   <$ char '/'
  , uMod      <$ char '%'
  , uLessE    <$ try (string "<=")
  , uLess     <$ char '<'
  , uGreaterE <$ try (string ">=")
  , uGreater  <$ char '>'
  , uEquals   <$ try (string "==")
  ]

-- | Lex one alphanumeric token
word_token :: Lexer Token
word_token = to_token <$> word
  where
    to_token "true"  = BoolTok True
    to_token "false" = BoolTok False
    to_token "if"    = If
    to_token "then"  = Then
    to_token "else"  = Else
    to_token "fix"   = FixTok
    to_token "let"   = LetTok
    to_token "in"    = InTok
    to_token other   = Name other

-- | Lex one word
word :: Lexer String
word = ((:) <$> (letter <|> char '_') <*>
                 (many (alphaNum <|> char '_')))
