type Parser a = String -> [(a,String)]

item :: Parser Char
item = \inp -> case inp of
                [] -> []
                (x:xs) -> [(x,xs)]

failure :: Parser a
failure = \inp -> []

myReturn :: a -> Parser a
myReturn v = \inp -> [(v,inp)]

parse :: Parser a -> String -> [(a,String)]
parse p inp = p inp

(+++) :: Parser a -> Parser a -> Parser a
p +++ q = \inp -> case p inp of
                  []  -> parse q inp
                  [(v,out)] -> [(v,out)]

--myP :: Parser (Char,Char)
--myP = do  x <- item
--          z <- item
--          y <- item
--          return (x,y)




