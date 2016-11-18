module Rand
  ( Rand
  , toIO
  , fromIO
  , rand
  ) where

import Crypto.Random
import Data.Word
import Data.ByteString

-- implementing a state transformer monad around IO
-- We should be using library functions to achieve this
-- However, good exercise to go through the details

data Rand a = Rand { runRand :: State -> IO (a, State) }
type State = SystemRandom 

-- in case we need to export a constructor: hiding internals
state :: (State -> IO (a, State)) -> Rand a
state = Rand

-- Rand can be turned into a monad
instance Monad Rand where
  return a = state $ \s -> return (a, s)
  m >>= f  = state $ \s -> do -- inside IO monad
    (a, s')   <- runRand m s
    (b, s'')  <- runRand (f a) s'
    return (b, s'')


-- A Rand action together with an initial state can be translated into
-- an IO action. The initial state can be retrieved as an IO action.
-- Hence, a Rand action should lead to a natural IO action:

toIO :: Rand a -> IO a
toIO m = do
  g <- newGenIO           -- newGenIO :: CryptoRandomGen g => IO g (initial state)
  (a, g') <- runRand m g  -- running Rand action from initial state
  return a                -- throwing final state away, simply returning value


-- main API function
rand :: Int -> Rand ByteString
rand n = state $ \s -> do -- inside the IO monad
  case genBytes n s of
    Left e            -> error $ show e
    Right (bytes, s') -> return (bytes, s')

fromIO :: IO a -> Rand a
fromIO m = state $ \s -> do -- inside the IO monad
  a <- m                    -- run IO action
  return (a, s)             -- no change in state





