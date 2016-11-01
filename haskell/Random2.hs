import Control.Applicative (Applicative, liftA2)
import System.Random

-- randomRIO :: Random a => (a, a) -> IO a
-- liftA2 :: Applicative f => (a -> b -> c) -> f a -> f b -> f c

rollDiceIO :: IO (Int, Int)
rollDiceIO = liftA2 (,) (randomRIO (1,6)) (randomRIO (1,6))

rollNDiceIO :: Int -> IO [Int]
rollNDiceIO n
  | n <= 0    = return []
  | otherwise = go n []
  where
    go :: Int -> [Int] -> IO [Int]
    go 0 list = return list
    go n list = do
      dice <- randomRIO(1,6)
      go (n - 1) (dice : list)

-- random :: (RandomGen g, Random a) => g -> (a, g)
-- mkStdGen :: Int -> StdGen (StdGen instance of RandomGen)


g = mkStdGen 0  -- 0 is our seed here

test1 = random g :: (Int, StdGen)

test2 = fst . random $ g :: Int -- rather useless, always returns the same value

test3 = randomR (1,6) g  :: (Int, StdGen)


clumsyRollDice :: (Int, Int)
clumsyRollDice = (n, m)
  where
  (n, g) = randomR (1,6) (mkStdGen 0)
  (m, _) = randomR (1,6) g

rollDice :: RandomGen a => a -> ((Int, Int), a)
rollDice g = ((n, m), g2)
  where
  (n, g1) = randomR (1,6) g
  (m, g2) = randomR (1,6) g1  

-- One constructor and one field --> newtype
newtype State s a = State { run :: s -> (a, s) }

state :: (s -> (a, s)) -> State s a
state f = State f

instance Monad (State s) where
  return x  = state $ \s -> (x, s)
  m >>= f   = state $ \s ->
    let (x, t) = run m s  -- running first action in state s
    in run (f x) t        -- running second action in new state t

put :: s -> State s ()
put s = state $ \_ -> ((), s)

get :: State s s 
get = state $ \s -> (s, s)

evalState :: State s a -> s -> a
evalState m s = fst $ run m s

execState :: State s a -> s -> s
execState m s = snd $ run m s


type Rand = State StdGen  -- state monad 'Rand'

rollDie :: Rand Int
rollDie = state $ randomR(1,6)

-- same function, written in verbose way
rollDie' :: Rand Int
rollDie' = do generator <- get
              let (value, newGen) = randomR(1,6) generator
              put newGen
              return value

test4 = evalState rollDie (mkStdGen 0)

rollDice' :: Rand (Int, Int)
-- rollDice' = liftA2 (,) rollDie rollDie
rollDice' = do
  x <- rollDie
  y <- rollDie
  return (x, y)

test5 = evalState rollDice' (mkStdGen 666)

rollNDice :: Int -> Rand [Int]
rollNDice n 
  | n <= 0    = return []
  | otherwise = go n []
  where
  go :: Int -> [Int] -> Rand [Int] 
  go 0 list = return list
  go n list = do
    x <- rollDie
    go (n - 1) (x : list)


test6 = evalState (rollNDice 100) (mkStdGen 156)

instance Functor (State s) where
  fmap f m = state $ \s ->
    let (x, t) = run m s
    in (f x, t) 

modify :: (s -> s) -> State s ()
modify update = state $ \s -> ((), update s)

gets :: (s -> a) -> State s a
gets peek = state $ \s -> (peek s, s)

-- random :: (RandomGen g, Random a) => g -> (a, g)
getRandom :: Random a => Rand a
getRandom = state random

test7 = evalState getRandom (mkStdGen 0) :: Bool
test8 = evalState getRandom (mkStdGen 0) :: Char
test9 = evalState getRandom (mkStdGen 0) :: Double
test10 = evalState getRandom (mkStdGen 0) :: Integer


