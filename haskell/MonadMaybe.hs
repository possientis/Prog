-- Attempting to understand Maybe as a monad

data M a = None | Some a deriving Show

instance Monad M where 
  return = Some
  k >>= f = case k of
    None    -> None
    Some x  -> f x
  fail _ = None

divide1 :: (Eq a, Fractional a) => a -> a -> a
divide1 x y = x / y 

divide2 :: (Eq a, Fractional a) => a -> a -> M a
divide2 x y
  | y == 0    = None
  | otherwise = Some (x / y)


-- ugly code
divide3 :: (Eq a, Fractional a) => M a -> M a -> M a
divide3 n m = case n of
  None    -> None
  Some x  -> case m of
    None    -> None
    Some y  -> case y of
      0 -> None
      _ -> Some (x / y) 

-- unreadable code 
divide4 :: (Eq a, Fractional a) => M a -> M a -> M a
divide4 n m = n >>= (\x -> 
              m >>= (\y -> 
                case y of
                  0 -> fail "Division by zero error"
                  _ -> return $ x / y ))

-- nice and readable
divide5 :: (Eq a, Fractional a) => M a -> M a -> M a
divide5 n m = do
  x <- n
  y <- m
  case y of
    0 -> fail "Division by zero error"
    _ -> return $ x / y




