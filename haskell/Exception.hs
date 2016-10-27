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

instance Exception SomeCompilerException

compilerExceptionToException :: Exception e => e -> SomeException
compilerExceptionToException = toException . SomeCompilerException


