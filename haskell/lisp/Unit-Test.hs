import Test.HUnit
import System.Exit

import Test_Parse

tests = TestList
  [ test_Parse
  ]


main = do
  counts <- runTestTT tests
  if failures counts  /= 0
    then exitWith $ ExitFailure 1
    else exitWith $ ExitSuccess
