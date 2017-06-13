import Test.HUnit
import Test_Eq
import Test_Show
import Test_Functor
import Test_Variable
import Test_SubFormula
import Test_Substitution
import Test_Valid
import Test_Admissible
import Test_AlphaEquiv
import Test_MinimalTransform

import System.Exit



tests = TestList 
  [ test_Eq, test_Functor, test_Show, test_Variable, test_SubFormula
  , test_Substitution, test_Valid, test_Admissible, test_AlphaEquiv
  , test_MinimalTransform
  ]

main = do
  counts <- runTestTT tests
  if failures counts  /= 0
    then exitWith $ ExitFailure 1
    else exitWith $ ExitSuccess




