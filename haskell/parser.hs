module Parser(Parser,apply,parse) where
import Data.Char
import Control.Monad

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
spot p = char >>= \x -> (guard (p x) >> return x)
