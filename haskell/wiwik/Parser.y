{
module Parser (
    parseExpr,
) where

import Lexer
import Syntax
import Control.Monad.Except
}
-- Lexer structure 
%tokentype { Token }

%token
    let     { TokenLet }
    true    { TokenTrue }
    false   { TokenFalse }
    in      { TokenIn }
    NUM     { TokenNum $$ }
    VAR     { TokenSym $$ }
    '\\'    { TokenLambda }
    '->'    { TokenArrow }
    '='     { TokenEq }
    '+'     { TokenAdd }
    '-'     { TokenSub }
    '*'     { TokenMul }
    '('     { TokenLParen }
    ')'     { TokenRParen }

-- Parser monad
%monad { Except String } { (>>=) } { return }
%error { parseError }

-- EntryPoint
%name expr

-- Operators
%left '+' '-'
%left '*'
%%

Expr : let VAR '=' Expr in Expr     { App (Lam $2 $6) $4 }
     | '\\' VAR '->' Expr           { Lam $2 $4 }
     | Form                         { $1 }

Form : Form '+' Form                { Op Add $1 $3 }
     | Form '-' Form                { Op Sub $1 $3 }
     | Form '*' Form                { Op Mul $1 $3 }
     | Fact                         { $1 }

Fact : Fact Atom                    { App $1 $2 }
     | Atom                         { $1 }

Atom : '(' Expr ')'                 { $2 }
     | NUM                          { Lit (LInt $1) }
     | VAR                          { Var $1 }
     | true                         { Lit (LBool True) }
     | false                        { Lit (LBool False) }


