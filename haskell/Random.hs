import System.Random
import Control.Monad.State

rand :: IO Int
rand = getStdRandom(randomR (0,100))

-- get the same 'random' number twice
twoBadRandoms :: RandomGen g => g -> (Int, Int)
twoBadRandoms gen = (fst $ random gen, fst $ random gen)

-- getStdGen ::  IO StdGen

test1 = fmap twoBadRandoms getStdGen  -- :: IO (Int, Int)


twoGoodRandoms :: RandomGen g => g -> ((Int, Int), g)
twoGoodRandoms gen = let (a, gen') = random gen
                         (b, gen'') = random gen'
                      in ((a,b), gen'')

test2 = fmap twoGoodRandoms getStdGen -- :: IO ((Int, Int), StdGen)
test3 = fmap fst test2                -- :: IO (Int, Int)

type RandomState a = State StdGen a


getRandom :: Random a => RandomState a
getRandom = do
  gen <- get
  let (val, gen') = random gen
  put gen'
  return val


getTwoRandoms :: Random a => RandomState (a,a)
getTwoRandoms = liftM2 (,) getRandom getRandom


runTwoRandoms :: IO (Int, Int)
runTwoRandoms = do
  oldState <- getStdGen
  let (result, newState) = runState getTwoRandoms oldState
  setStdGen newState
  return result



