module Parser 
  ( Parser(Parser, run)
  , char
  , greed
  , match
  , option
  , plus
  , plus'
  , sat
  , range
  , star
  , star'
  , (<|>)
  , (&&&)
  , (<&&>)
  , (|||)
  ) where

import Control.Applicative
import Control.Monad

-- attempting to unite the operations of lexical analysis and parsing 
-- of token streams into a single monad. So typically the variable type
-- 'b' is Char when it comes to reducing a String into a list of tokens,
-- while 'b' is some token type Token when it comes to parsing the list
-- of token based on a certain grammar.

data Parser b a = Parser { run :: [b] -> [(a, [b])] }

instance Functor (Parser b) where
  fmap = liftM

instance Applicative (Parser b) where
  pure  = return
  (<*>) = ap

instance Monad (Parser b) where
  return a  = Parser (\cs -> [(a,cs)])
  m >>= f   = Parser (\cs -> concat [ run (f a) cs' | (a, cs') <- run m cs ]) 

instance Alternative (Parser b) where
  empty = mzero
  (<|>) = mplus

instance MonadPlus (Parser b) where
  mzero = Parser (\cs -> [])        -- no parse, not to be confused with return []
  mplus p q = Parser (\cs -> run p cs ++ run q cs)

sat :: (b -> Bool) -> Parser b [b]
sat pred = Parser f where
  f []      = []
  f (c:cs)  = if pred c then [([c],cs)] else []

itemParser :: Parser b [b]
itemParser = sat $ const True

char :: (Eq b) => b -> Parser b [b]
char b = sat (== b)

range :: (Eq b) => [b] -> Parser b [b]
range []      = error "range: empty list"
range [c]     = char c
range (c:cs)  = (char c) <|> range cs

(&&&) :: Parser b a -> Parser b a' -> Parser b (a,a')
(&&&) par1 par2 = do { a   <- par1; a'  <- par2; return (a,a') }

(<&&>) :: Parser b [b] -> Parser b [b] -> Parser b [b]
(<&&>) par1 par2 = do { s1 <- par1; s2 <- par2; return $ s1 ++ s2 }

  
(|||) :: Parser b a -> Parser b a' -> Parser b (Either a a')
(|||) par1 par2 =  Left <$> par1 <|> Right <$> par2

star  :: Parser b a -> Parser b [a]
star p = return [] <|> plus p

plus :: Parser b a -> Parser b [a]
plus p = do { a <- p; as <- star p; return (a:as) }


plus' :: Parser b [a] -> Parser b [a]
plus' = liftM concat . plus

star' :: Parser b [a] -> Parser b [a]
star' = liftM concat . star

-- TODO use these parsers to clean up existing code 
sepby :: Parser b a -> Parser b a' -> Parser b [a]
p `sepby` sep = return [] <|> (p `sepby1` sep)

sepby1 :: Parser b a -> Parser b a' -> Parser b [a]
p `sepby1` sep = do
  a <- p
  as <- star $ do { sep; p }
  return (a:as)


-- transforms a parser argument into a 'greedy' parser, 
-- namely a parser which among ambiguous parsing results,
-- only keeps those results which minimize the length of
-- the remaining string of type [b]. 
-- The function 'minimum' will throw an exception on []
-- However, if xs = [] then filter should return [] and
-- the sat 'pred' should not be evaluated, so the
-- function 'minimum' should not be called at all.  
greed :: Parser b a -> Parser b a
greed par = Parser f where
  f cs              = filter pred xs where
    xs              = run par cs
    pred (a,cs')    = (length cs' == minLength)
    minLength       = minimum $ map (length . snd) xs

option :: Parser b [b] -> Parser b [b]
option par = par <|> return []

match :: (Eq b) => [b] -> Parser b [b]
match []  = return []
match (c:cs) = char c <&&> match cs 


