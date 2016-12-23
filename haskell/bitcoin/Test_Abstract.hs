module Test_Abstract
  ( logMessage
  , checkEquals
  , checkException
  , checkCondition
  , getRandomBytes
  ) where

import Rand
import System.Exit
import Data.ByteString hiding (putStrLn)

logMessage :: String -> Rand ()
logMessage s = liftIO $ putStrLn s

checkEquals :: (Eq a, Show a) => a -> a -> String -> Rand ()
checkEquals x y msg =
  if x /= y 
    then do
      logMessage (msg ++ ": checkEquals failure")
      logMessage ("left = "  ++ show x)
      logMessage ("right = " ++ show y)
      liftIO exitFailure
    else if y /= x
      then do 
        logMessage (msg ++ ": checkEquals failure")
        logMessage "override of (==) is not symmetric"
        logMessage "left == right is true while right == left is false"
        liftIO exitFailure
      else
        return ()

checkCondition :: Bool -> String -> Rand ()
checkCondition cond msg =
  if not cond
    then do
      logMessage (msg ++ ": checkCondition failure")
      liftIO exitFailure
    else
      return ()

checkException :: Rand a -> String -> String -> Rand ()
checkException action eName msg =
  try ( do
    x <- action
    logMessage $ msg ++ ": checkException failure: no exception detected"
    liftIO exitFailure)
    (\e -> if (exceptionName e) /= eName 
      then do
        logMessage (msg ++ ": checkException failure: wrong exception type")
        logMessage ("Expected: " ++ eName)
        logMessage ("Actual: " ++ exceptionName e)
        liftIO exitFailure
      else 
        return ())
   
     
  

