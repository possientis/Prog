{-# LANGUAGE TemplateHaskell #-}

import Control.Monad.Identity

import Language.Haskell.TH.Syntax

import Text.Parsec
import Text.Parsec.String (Parser)
import Text.Parsec.Language (emptyDef)

import qualified Text.Parsec.Expr as Ex
import qualified Text.Parsec.Token as Tok

data Expr 
    = Tr
    | Fl
    | Zero
    | Succ Expr
    | Pred Expr
    deriving (Eq,Show)

instance Lift Expr where
    lift Tr         = [| Tr |]
    lift Fl         = [| Fl |]
    lift Zero       = [| Zero |]
    lift (Succ a)   = [| Succ a |]
    lift (Pred a)   = [| Pred a |]

type Op = Ex.Operator String () Identity

lexer :: Tok.TokenParser ()
lexer = Tok.makeTokenParser emptyDef

parens :: Parser a -> Parser a
parens = Tok.parens lexer

reserved :: String -> Parser ()
reserved = Tok.reserved lexer

