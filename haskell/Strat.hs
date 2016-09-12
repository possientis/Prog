-- see module Control.Parallel.Strategies

import Control.Parallel (par)

type Done = ()

-- An evaluation strategy performs no computation; it simply ensures 
-- that a value is evaluated to some extent.
type Strategy a = a -> Done

-- simplest strategy does nothing
rO :: Strategy a
rO _ = ()

-- next is rwhnf , which evaluates a value to WHNF:
rwhnf :: Strategy a
rwhnf x = x `seq` ()

class NFData a where
  rnf :: Strategy a
  rnf = rwhnf

instance NFData Char
instance NFData Int

instance NFData a => NFData (Maybe a) where
  rnf Nothing = ()
  rnf (Just x) = rnf x

{- ... and so on ... -}


parList :: Strategy a -> Strategy [a]
parList strat []      = ()
parList strat (x:xs)  = strat x `par` (parList strat xs) 

-- seperating algorithm from strategy
parMap :: Strategy b -> (a -> b) -> [a] -> [b]
parMap strat f xs = map f xs `using` parList strat

using :: a -> Strategy a -> a
using x s = s x `seq` x

{-
vectorSum :: (NFData a, Num a) => [a] -> [a] -> [a]
vectorSum = parZipWith rnf (+)
-}



