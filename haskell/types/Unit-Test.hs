import Test.HUnit
import Test_eval1
import Test_eval
import Test_isNumerical
import Test_isVal

import System.Exit


tests = TestList 
      [ test_eval1, test_eval, test_isNumerical, test_isVal
      ]


main = do
  counts <- runTestTT tests
  if failures counts /= 0
    then exitWith $ ExitFailure 1
    else exitWith $ ExitSuccess
