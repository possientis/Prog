newtype M a = M { runM :: State -> [(a, State)] }

type State = String

stateM :: (State -> [(a, State)]) -> M a
stateM = M


data Term = Con Int | Div Term Term

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

(|+|) :: M a -> M a -> M a
m |+| n = stateM $ \s -> runM m s ++ runM n s




