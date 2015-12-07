module Parser(Parser, apply, parse, spot, token, mplus) where
import Data.Char
import Control.Monad
import Test.QuickCheck

-- Phil Wadler "In fact, you can build parsers over arbitrary monads
-- rather than just the list monad, as long as it has sums" (MonadPlus)

-- The type of parsers
newtype Parser a = MkParser (String -> [(a, String)])

-- Apply a parser
apply :: Parser a -> String -> [(a, String)]
apply (MkParser f) s = f s 

-- Return parsed value, assuming at least one successful parse
parse :: Parser a -> String -> a
parse m s = one [ x | (x,t) <- apply m s, t == "" ]
  where
  one []                  = error "no parse"
  one [x]                 = x
  one xs | length xs > 1  = error "ambiguous parse"

-- Parsers form a monad

-- class Monad m where
--  return  :: a -> m a
--  (>>=)   :: m a -> (a -> m b) -> m b 

instance Monad Parser where
  return x = MkParser (\s -> [(x,s)])
  m >>= k  = MkParser (\s ->
                        [ (y, u) |
                          (x, t) <- apply m s,
                          (y, u) <- apply (k x) t ]) 

-- Parsers form a monad with sums
--  class MonadPlus m where
--    mzero :: m a
--    mplus :: m a -> m a -> m a

instance MonadPlus Parser where
  mzero = MkParser (\s -> [])
  mplus m n = MkParser (\s -> apply m s ++ apply n s)


-- Parse one character
char :: Parser Char
char = MkParser f where
  f [] = []
  f (c:s) = [(c,s)]

-- guard :: MonadPlus m => Bool -> m ()
-- guard False = mzero
-- guard True = return ()

-- Parse a character satisfying a predicate (e.g. isDigit)
spot :: (Char -> Bool) -> Parser Char
--spot p = do { c <- char; guard (p c); return c }
spot p = char >>= \x -> (guard (p x) >>= \y -> return x)

-- Match a given character
token :: Char -> Parser Char
token c = spot (== c)

-- just for fun
test1 = (spot isDigit) >>= (\x -> token '+' >> (spot isDigit) >>= \y -> return (digitToInt x + digitToInt y))

-- Perform a list of commands, returning a list of values
-- sequence :: Monad m => [m a] -> m [a]
-- sequence [] = []
-- sequence (m:ms) = do {
--                        x   <- m;
--                        xs  <- sequence ms;
--                        return (x:xs)
--                      }

-- just for fun
test2 = sequence [token 'w',token 'h',token 'e', token 'n']


-- match a given string (defined two ways)
match :: String -> Parser String
match []  = return []
match (x:xs) = token x >>= (\y -> match xs >>= (\ys -> return (y:ys)))
-- match (x:xs) = do { y  <- token x;
--                     ys <- match xs;
--                     return (y:ys)
--                }

match' :: String -> Parser String
match' xs = sequence (map token xs) -- amazing !!


test3 = mplus (token 'a') (token 'b') 
test4 = spot (\x -> (x == 'a') || (x == 'c'))

check1 :: String -> Bool
check1 s = (apply test3 s) == (apply test4 s)


-- match zero  or more occurences
star :: Parser a -> Parser [a]
star p = plus p `mplus` return []

-- match one or more occurences
plus :: Parser a -> Parser [a]
plus p = p >>= (\x -> star p >>= (\xs -> return (x:xs)))

test5 = star (token 'a')

-- match a natural number
parseNat :: Parser Int
parseNat = plus (spot isDigit) >>= (\s -> return (read s))

-- more fun
test6 = star (token 'a' `mplus` token 'b') >>= (\x -> plus (token 'b' `mplus` token 'c') >>= \y -> return (x,y))

-- match a negative number
parseNeg :: Parser Int
parseNeg = token '-' >> parseNat >>= (\n -> return (-n))

-- match an integer
parseInt :: Parser Int
parseInt = mplus parseNat parseNeg


