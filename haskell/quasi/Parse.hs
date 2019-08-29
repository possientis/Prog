import Text.ParserCombinators.Parsec

import Expr

small :: Parser Char
small = lower <|> char '_'

large :: Parser Char
large = upper

idchar :: Parser Char
idchar = small <|> large <|> digit <|> char '\''

lexeme :: Parser a -> Parser a
lexeme p = do { x <- p; spaces; return x }

symbol :: String -> Parser String
symbol name = lexeme (string name)

parens :: Parser a -> Parser a
parens p = between (symbol "(") (symbol ")") p

ident :: Parser String
ident = do { c <- small; cs <- many idchar; return (c:cs) }

antiInt :: Parser Expr
antiInt = lexeme $ do { _ <- symbol "$int:"; i <-ident; return $ EAntiInt i }

antiExp :: Parser Expr
antiExp = lexeme $ do { _ <- symbol "$exp:"; i <-ident; return $ EAntiExp i }

integer :: Parser Expr
integer = lexeme $ do { ds <- many1 digit; return $ ELitInt (read ds) }

addop :: Parser (Expr -> Expr -> Expr)
addop =  do { _ <- symbol "+"; return $ EBinop OpAdd }
     <|> do { _ <- symbol "-"; return $ EBinop OpSub }

mulop :: Parser (Expr -> Expr -> Expr)
mulop =  do { _ <- symbol "*"; return $ EBinop OpMul }
     <|> do { _ <- symbol "/"; return $ EBinop OpDiv }

expr :: Parser Expr
expr = term `chainl1` addop

factor :: Parser Expr 
factor = parens expr <|> integer <|> antiExp <|> antiInt

term :: Parser Expr
term = factor `chainl1` mulop

parseExpr :: Monad m => (String, Int, Int) -> String -> m Expr
parseExpr (file, line, col) s =
    case runParser p () "" s of
        Left err    -> fail $ show err
        Right e     -> return e
    where
        p :: Parser Expr
        p = do
            pos <- getPosition
            setPosition $
                (flip setSourceName)   file $
                (flip setSourceLine)   line $
                (flip setSourceColumn) col  $
                pos
            spaces
            e <- expr
            eof
            return e


 


