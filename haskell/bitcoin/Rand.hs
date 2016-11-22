module Rand
  ( Rand
  , RandException
  , randException
  , exceptionName
  , throw
  , try
  , toIO
  , fromIO
  , getRandomBytes
  ) where

import Crypto.Random
import Data.Word
import Data.ByteString

-- Exception Handling

data RandException  = RE { name :: String, message :: String }
type Name           = String
type Message        = String

randException :: Name -> Message -> RandException
randException = RE

exceptionName :: RandException -> String
exceptionName = name


instance Show RandException where
  show e = "RandException: " ++ (name e) ++ ". " ++ (message e)

fromGenError :: GenError -> RandException
fromGenError e = case e of
  RequestedTooManyBytes  -> RE "RequestedTooManyBytes" "GenError"
  RangeInvalid           -> RE "RangeInvalid"          "GenError" 
  NeedReseed             -> RE "NeedReseed"            "GenError"
  NotEnoughEntropy       -> RE "NotEnoughEntropy"      "GenError"
  NeedsInfiniteSeed      -> RE "NeedsInfiniteSeed"     "GenError"
  GenErrorOther msg      -> RE "GenErrorOther"         msg

throw :: RandException -> Rand a
throw e = state $ \s -> return $ Left e 

try :: Rand a -> (RandException -> Rand a) -> Rand a
try action catch = state $ \s -> do -- inside the IO monad
  actionResult  <- runRand action s -- running action
  case actionResult of
    Left e        -> runRand (catch e) s
    Right (a, s') -> return $ Right (a, s')
 
-- The Rand Monad

-- implementing a state transformer monad around IO and 
-- Either (to emulate exception handling)
-- We should be using library functions to achieve this
-- However, good exercise to go through the details

data Rand a         = Rand { runRand :: State -> IO (Result a) }
type Result a       = Either RandException (a, State)
type State          = SystemRandom 

-- in case we need to export a constructor: hiding internals
state :: (State -> IO (Result a)) -> Rand a
state = Rand


-- Rand can be turned into a monad
instance Monad Rand where
  return a = state $ \s -> return $ Right (a, s)  -- action never throws
  m >>= f  = state $ \s -> do -- inside IO monad
    first <- runRand m s
    case first of
      Left e        -> return $ Left e
      Right (a, s') -> do
        second  <- runRand (f a) s'
        case second of
          Left e          -> return $ Left e
          Right (b, s'')  -> do
            return $ Right (b, s'')

{-
instance Functor Rand where
  fmap f m = state $ \s -> do
    x <- runRand m s 
    case x of
      Left e        -> return $ Left e
      Right (a, s') -> return $ Right (f a, s')
-}

-- A Rand action together with an initial state can be translated into
-- an IO action. The initial state can be retrieved as an IO action.
-- Hence, a Rand action should lead to a natural IO action:

toIO :: Rand a -> IO a
toIO m = do                   -- newGenIO :: CryptoRandomGen g => IO g
  g <- newGenIO               -- retrieving initial state 
  result <- runRand m g       -- running Rand action from initial state
  case result of
    Left e        -> error (show e)
    Right (a, g') -> return a -- throwing final state away, simply returning value


-- main API function
getRandomBytes:: Int -> Rand ByteString
getRandomBytes n = state $ \s -> do -- inside the IO monad
  case genBytes n s of
    Left e            -> return $ Left $ fromGenError e
    Right (bytes, s') -> return $ Right (bytes, s')

fromIO :: IO a -> Rand a
fromIO m = state $ \s -> do -- inside the IO monad
  a <- m                    -- run IO action
  return $ Right (a, s)     -- no change in state

