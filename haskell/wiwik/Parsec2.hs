{-# LANGUAGE OverloadedStrings #-}

import Prelude hiding (getLine)

import Data.Text hiding (foldl1)
import Data.Text.IO

import Data.Functor.Identity

import Text.Parsec
import Text.Parsec.Text
import Text.Parsec.Language
import Text.Parsec.Token hiding (parens, reservedOp)

import qualified Text.Parsec.Token as Tok (parens, reservedOp)

data Expr
    = Var Text
    | App Expr Expr
    | Lam Text Expr
    deriving (Show)


lexer :: GenTokenParser Text () Identity
lexer = makeTokenParser style

style :: GenLanguageDef Text () Identity
style   = emptyDef
        { commentStart      = "{-"
        , commentEnd        = "-}"
        , commentLine       = "--"
        , nestedComments    = True
        , identStart        = letter
        , identLetter       = alphaNum <|> oneOf "_'"
        , opStart           = opLetter style
        , opLetter          = oneOf ":!#$%&*+./<=>?@\\^|-~"
        , reservedOpNames   = []
        , reservedNames     = []
        , caseSensitive     = True
        }

parens :: Parser a -> Parser a
parens = Tok.parens lexer

reservedOp :: Text -> Parser ()
reservedOp op = Tok.reservedOp lexer (unpack op)

ident :: Parser Text
ident = pack <$> identifier lexer

contents :: Parser a -> Parser a
contents p = do
    whiteSpace lexer
    r <- p
    eof
    return r

var :: Parser Expr
var = do
    var <- ident
    return (Var var)

app :: Parser Expr
app = do
    e1 <- expr
    e2 <- expr
    return (App e1 e2)

fun :: Parser Expr
fun = do
    reservedOp "\\"
    binder <-ident
    reservedOp "."
    rhs <- expr
    return (Lam binder rhs)

expr :: Parser Expr
expr = do
    es <- many1 aexp
    return (foldl1 App es)

aexp :: Parser Expr
aexp = fun <|> var <|> (parens expr)


test :: Text -> Either ParseError Expr
test = parse (contents expr) "<stdin>"

repl :: IO ()
repl = do
    str <- getLine
    print (test str)
    repl

main :: IO ()
main = repl




