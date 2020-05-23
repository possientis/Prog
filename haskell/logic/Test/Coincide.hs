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
    testCoincideCons
    testCoincideApp

testCoincideMap :: Spec
testCoincideMap = it "Checked coincide map property" $
    property $ propCoincideMap

testCoincideIncl :: Spec
testCoincideIncl = it "Checked coincide incl property" $ 
    property $ propCoincideIncl

testCoincideCons :: Spec
testCoincideCons = it "Checked coincide cons property" $ 
    property $ propCoincideCons

testCoincideApp :: Spec
testCoincideApp = it "Checked coincide app property" $ 
    property $ propCoincideApp

propCoincideMap :: (Var -> Var) -> (Var -> Var) -> [Var] -> Bool
propCoincideMap f g xs = (not $ coincide xs f g) || map f xs == map g xs

propCoincideIncl :: (Var -> Var) -> (Var -> Var) -> [Var] -> [Var] -> Bool
propCoincideIncl f g xs ys = (not $ (ys <== xs) && coincide xs f g) ||
    coincide ys f g

propCoincideCons :: (Var -> Var) -> (Var -> Var) -> Var -> [Var] -> Bool
propCoincideCons f g x xs = (not $ coincide (x : xs) f g) || coincide xs f g


propCoincideApp :: (Var -> Var) -> (Var -> Var) -> [Var] -> [Var] -> Bool
propCoincideApp f g xs ys = (not $ coincide xs f g) || (not $ coincide ys f g) ||
    coincide (xs ++ ys) f g



