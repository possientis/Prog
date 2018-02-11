-- **Begin Haskell Syntax**
{
{-# OPTIONS_GHC -w #-}

module Lexer (
    Token(..),
    scanTokens
) where

import Syntax
}
-- **End Haskell Syntax**

-- **Begin Alex Syntax**
%wrapper "basic"

$digit = 0-9
$alpha = [a-zA-Z]
$eol   = [\n]

tokens :-

    -- whitespace insensitive
    $eol                            ;
    $white+                         ;
    -- comments
    "#".*                           ;

    -- syntax
    let                             { \s -> TokenLet }
    True                            { \s -> TokenTrue }
    False                           { \s -> TokenFalse }
    in                              { \s -> TokenIn }
    $digit+                         { \s -> TokenNum (read s) }
    "->"                            { \s -> TokenArrow }
    \=                              { \s -> TokenEq }
    \\                              { \s -> TokenLambda }
    [\+]                            { \s -> TokenAdd }
    [\-]                            { \s -> TokenSub }
    [\*]                            { \s -> TokenMul }
    \(                              { \s -> TokenLParen }
    \)                              { \s -> TokenRParen }
    $alpha [$alpha $digit \_ \']*   { \s -> TokenSym s }

{

data Token 
  = TokenLet
  | TokenTrue
  | TokenFalse
  | TokenIn
  | TokenLambda
  | TokenNum Int
  | TokenSym String
  | TokenArrow
  | TokenEq
  | TokenAdd
  | TokenSub
  | TokenMul
  | TokenLParen
  | TokenRParen
  | TokenEOF
  deriving (Eq,Show)

scanTokens :: String -> [Token]
scanTokens = alexScanTokens

}
