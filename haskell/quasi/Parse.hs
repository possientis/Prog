import Text.ParserCombinators.Parsec

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


