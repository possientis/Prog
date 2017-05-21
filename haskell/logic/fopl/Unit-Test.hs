import Test.HUnit
import Test_Eq
import Test_Show
import Test_Functor
import Test_Variable
import Test_SubFormula

import System.Exit



tests = TestList 
  [ test_Eq, test_Show, test_Functor, test_Variable, test_SubFormula
  ]

main = do
  counts <- runTestTT tests
  if failures counts  /= 0
    then exitWith $ ExitFailure 1
    else exitWith $ ExitSuccess




