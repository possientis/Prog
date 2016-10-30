{-# LANGUAGE DeriveDataTypeable, ScopedTypeVariables, ExistentialQuantification #-}

import Control.Exception
import Data.Typeable

data MyException = ThisException | ThatException
  deriving (Show, Typeable)

instance Exception MyException

this = SomeException ThisException
that = SomeException ThatException 

testThis = fromException this :: Maybe MyException
testThat = fromException that :: Maybe MyException

main :: IO ()
main = do
  handle  (\(e::SomeException) -> print $ "Exception was caught: " ++ show e)
          (putStrLn $ show $ foldl1 (+) ([]::[Int]))


test1 :: IO ()
test1 = do
  throw ThisException `catch` \e -> 
    putStrLn $ "Caught " ++ show (e :: MyException)

data SomeCompilerException = forall e . Exception e => SomeCompilerException e
  deriving Typeable

instance Show SomeCompilerException where
  show (SomeCompilerException e) = show e

instance Exception SomeCompilerException where

-- toException :: Exception e => e -> SomeException
-- we could define it ourselves
compilerExceptionToException :: Exception e => e -> SomeException
compilerExceptionToException = toException . SomeCompilerException

-- fromException :: Exception e => SomeException -> Maybe e
-- we can also define this ourselves, using 
-- cast :: (Typeable a, Typeable b) => a -> Maybe b

compilerExceptionFromException :: Exception e => SomeException -> Maybe e
compilerExceptionFromException x = do  -- do notation in the Maybe monad ....
  SomeCompilerException a <- fromException x
  cast a






test2 = SomeCompilerException ThisException

test3 :: IO ()
test3 = do
  print $ toException test2
  print $ compilerExceptionToException test2
  return ()


