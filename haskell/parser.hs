module Parser(Parser,apply,parse) where
import Data.Char
import Control.Monad

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

