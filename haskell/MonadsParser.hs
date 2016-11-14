import Data.Char
import Prelude hiding (iterate)

newtype M a = M { runM :: State -> [(a, State)] }

type State = String

stateM :: (State -> [(a, State)]) -> M a
stateM = M


data Term = Con Int | Div Term Term deriving (Show)

-- Definition: a parser is an object of type M a for some a
-- Definition: a parser m is unambiguous, if and only if
-- runM m s has length 0 or 1 for every possible state s

-- This is an unambiguous parser
item :: M Char
item = stateM $ \s -> 
  case s of
    []      -> []
    (x:xs)  -> [(x, xs)]


instance Monad M where
  return a  = stateM $ \s -> [(a, s)]
  m >>= f   = stateM $ \s -> 
    let list = runM m s in
      [(b, u) | (a, t) <- runM m s, (b, u) <- runM (f a) t] 
{-
      do
        (a, t) <- list
        (b, u) <- runM (f a) t
        return (b, u)
-}     

twoItems :: M (Char, Char)
twoItems = do
  a <- item
  b <- item
  return (a, b)

zero :: M a
zero = stateM $ \s -> []

-- alternation
(|+|) :: M a -> M a -> M a
m |+| n = stateM $ \s -> runM m s ++ runM n s

oneOrTwoItems :: M String
oneOrTwoItems = (item >>= \a -> return [a]) |+|
                (item >>= \a -> item >>= \b -> return [a,b])

-- filtering
(|>|) :: M a -> (a -> Bool) -> M a
m |>| p = m >>= \a ->
  if p a then return a else zero

letter :: M Char
letter = item |>| isLetter

digit :: M Int
digit = (item |>| isDigit) >>= \a -> return $ digitToInt a

lit :: Char -> M Char
lit c = item |>| (== c)

iterate :: M a -> M [a]
iterate m = (return []) |+| do
  a <- m
  as <- iterate m
  return (a:as) 

-- not a parser
asNumber :: [Int] -> Int
asNumber xs = go 0 xs where
  go :: Int -> [Int] -> Int
  go n [] = n
  go n (x:xs) = go ((10 * n) + x) xs

-- ambiguous parser
number1 :: M Int
number1 = do
  a   <- digit
  as  <- iterate digit
  return $ asNumber (a:as) 

-- biased choice
(|/|) :: M a -> M a -> M a
m |/| n = stateM $ \s ->
  let list = runM m s in
    if null list 
      then runM n s
      else list

reiterate :: M a -> M [a]
reiterate m = ( do 
  a <- m
  as <- reiterate m
  return (a:as) ) |/| return []

number :: M Int
number = do
  a <- digit
  as <- reiterate digit
  return $ asNumber (a:as)

-- BNF grammar for (fully parenthesised) term
-- term ::= number | '(' term '%' term ')'

term0 :: M Term
term0 =  (number >>= \a -> return $ Con a) |+| do
  lit '('
  t <- term0
  lit '%'
  u <- term0
  lit ')'
  return $ Div t u

-- BNF grammar where % should associate to the left
-- term ::= term  '%' factor | factor
-- factor ::= number | '(' term ')'

-- The first step of term is to apply term => infinite loop
-- This is called the 'left recursion problem'
term1 :: M Term
term1 = factor1 |+| do
  t <- term1
  lit '%'
  u <- factor1
  return $ Div t u

factor1 :: M Term
factor1 = (number >>= \a -> return $ Con a) |+| do
  lit '('
  t <- term1
  lit ')'
  return t


-- Need to rewrite grammar
-- term   ::= factor term'
-- term'  ::= '%' factor term' | ""

factor :: M Term
factor = (number >>= \a -> return $ Con a) |+| do
  lit '('
  t <- term1
  lit ')'
  return t

term :: M Term
term = do
  t <- factor
  term' t  

term' :: Term -> M Term
term' t = (do
  lit '%'
  u <- factor
  term' (Div t u)) |+| return t














