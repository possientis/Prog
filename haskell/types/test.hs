import Test_eval1
import Test_eval
import Test_isNumerical
import Test_isVal

import Test.HUnit

tests = TestList 
      [ test_eval1, test_eval, test_isNumerical, test_isVal
      ]


main = do
  runTestTT tests
