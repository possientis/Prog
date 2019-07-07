module  Test.Coincide
    (   specCoincide
    )   where

 
import  Test.Hspec
import  Test.QuickCheck
    
import Coincide
import Variable (Var)

specCoincide :: Spec
specCoincide = describe "Testing properties of coincide..." $
    sequence_ specsCoincide

specsCoincide :: [Spec]
specsCoincide  = [ testCoincideMap
                 ]

testCoincideMap :: Spec
testCoincideMap = it "Checked coincide map property" $
    property $ propCoincideMap

propCoincideMap :: (Var -> Var) -> (Var -> Var) -> [Var] -> Bool
propCoincideMap f g xs = (not $ coincide xs f g) || map f xs == map g xs

