module Parser 
  ( Parser(Parser, run)
  , char
  , greed
  , match
  , nil
  , option
  , plus
  , plus'
  , predicate
  , range
  , star
  , star'
  , (&&&)
  , (<&&>)
  , (+++)
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

nil :: Parser b [b]
nil = Parser (\cs -> [([],cs)])

predicate :: (b -> Bool) -> Parser b [b]
predicate pred = Parser f where
  f []      = []
  f (c:cs)  = if pred c then [([c],cs)] else []

itemParser :: Parser b [b]
itemParser = predicate $ const True

char :: (Eq b) => b -> Parser b [b]
char b = predicate (== b)

range :: (Eq b) => [b] -> Parser b [b]
range []      = error "range: empty list"
range [c]     = char c
range (c:cs)  = (char c) +++ range cs

(&&&) :: Parser b a -> Parser b a' -> Parser b (a,a')
(&&&) par1 par2 = do { a   <- par1; a'  <- par2; return (a,a') }

(<&&>) :: Parser b [b] -> Parser b [b] -> Parser b [b]
(<&&>) par1 par2 = (liftM (\(x,y) -> x++y)) (par1 &&& par2)

(+++) :: Parser b a -> Parser b a -> Parser b a 
(+++) par1 par2 = Parser (\cs -> run par1 cs ++ run par2 cs)
  
(|||) :: Parser b a -> Parser b a' -> Parser b (Either a a')
(|||) par1 par2 =  liftM Left par1 +++ liftM Right par2

plus :: Parser b a -> Parser b [a]
plus par = liftM (\x -> [x]) par +++
                 liftM (\(x,y) -> (x:y)) (par &&& (plus par))

star :: Parser b [b] -> Parser b [[b]]
star par = liftM (\x -> [x]) nil +++ plus par

plus' :: Parser b [b] -> Parser b [b]
plus' = liftM concat . plus

star' :: Parser b [b] -> Parser b [b]
star' = liftM concat . star

-- transforms a parser argument into a 'greedy' parser, 
-- namely a parser which among ambiguous parsing results,
-- only keeps those results which minimize the length of
-- the remaining string of type [b]. 
-- The function 'minimum' will throw an exception on []
-- However, if xs = [] then filter should return [] and
-- the predicate 'pred' should not be evaluated, so the
-- function 'minimum' should not be called at all.  
greed :: Parser b a -> Parser b a
greed par = Parser f where
  f cs              = filter pred xs where
    xs              = run par cs
    pred (a,cs')    = (length cs' == minLength)
    minLength       = minimum $ map (length . snd) xs

option :: Parser b [b] -> Parser b [b]
option par = par +++ nil

match :: (Eq b) => [b] -> Parser b [b]
match []  = nil
match (c:cs) = char c <&&> match cs 


