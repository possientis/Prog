module  Test.Coincide
    (   specCoincide
    )   where

 
import  Test.Hspec
import  Test.QuickCheck
    
import Coincide
import Include
import Variable (Var)

specCoincide :: Spec
specCoincide = describe "Testing properties of coincide..." $ do
    testCoincideMap
    testCoincideIncl

testCoincideMap :: Spec
testCoincideMap = it "Checked coincide map property" $
    property $ propCoincideMap

testCoincideIncl :: Spec
testCoincideIncl = it "Checked coincide incl property" $ 
    property $ propCoincideIncl

propCoincideMap :: (Var -> Var) -> (Var -> Var) -> [Var] -> Bool
propCoincideMap f g xs = (not $ coincide xs f g) || map f xs == map g xs

propCoincideIncl :: (Var -> Var) -> (Var -> Var) -> [Var] -> [Var] -> Bool
propCoincideIncl f g xs ys = (not $ (ys <== xs) && coincide xs f g) ||
    coincide ys f g

