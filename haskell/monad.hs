import Control.Monad

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


myFunc :: Int -> Maybe Int
myFunc 0 = Nothing
myFunc n = Just n

myAdd :: Maybe Int -> Maybe Int -> Maybe Int
myAdd mx my =
  case mx of
    Nothing -> Nothing
    Just x  -> case my of
                Nothing -> Nothing
                Just y  -> Just (x + y)

-- represents the 'bind' operator (>>=)
(£) :: Maybe a -> (a -> Maybe b) -> Maybe b
Nothing £ _ = Nothing
(Just x) £ f = f x

myReturn :: a -> Maybe a
myReturn x = Just x

yourAdd :: Maybe Int -> Maybe Int -> Maybe Int
yourAdd mx my =
  mx £ (\x ->
    my £ (\y ->
      return (x+y)))

hisAdd :: Maybe Int -> Maybe Int -> Maybe Int
hisAdd mx my = do
  x <- mx
  y <- my
  return (x + y)

herAdd :: Maybe Int -> Maybe Int -> Maybe Int
herAdd = liftM2 (+)


