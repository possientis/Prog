module  Test.Remove
    (   specRemove
    )   where

import  Test.Hspec
import  Test.QuickCheck

import Remove
import Include
import Injective
import Variable (Var)


specRemove :: Spec
specRemove = describe "Testing properties for remove..." $ 
    sequence_ specsRemove

specsRemove :: [Spec]
specsRemove  = [ testRemoveStill
               , testRemoveMon
               , testRemoveMapIncl
               , testRemoveXNotIn
               , testRemoveInj
               , testRemoveInj2
               , testRemoveIncl
               , testRemoveCharac
               ]


testRemoveStill :: Spec
testRemoveStill = it "Checked remove vs elem property" $
    property $ propRemoveStill

testRemoveMon :: Spec
testRemoveMon = it "Checked remove monotone property" $
    property $ propRemoveMon

testRemoveMapIncl :: Spec
testRemoveMapIncl = it "Checked remove map inclusion property" $ 
    property $ propRemoveMapIncl

testRemoveXNotIn :: Spec
testRemoveXNotIn = it "Checked remove 'not in' property" $ 
    property $ propRemoveXNotIn

testRemoveInj :: Spec
testRemoveInj = it "Checked remove first injective property" $ 
    property $ propRemoveInj

testRemoveInj2 :: Spec
testRemoveInj2 = it "Checked remove second injective property" $ 
    property $ propRemoveInj2

testRemoveIncl :: Spec
testRemoveIncl = it "Checked remove inclusion property" $ 
    property $ propRemoveIncl

testRemoveCharac :: Spec
testRemoveCharac = it "Checked remove characterization property" $ 
    property $ propRemoveCharac

propRemoveStill :: Var -> Var -> [Var] -> Bool
propRemoveStill x y xs = x == y || y `notElem` xs || y `elem` (remove x xs) 


propRemoveMon :: Var -> [Var] -> [Var] -> Bool
propRemoveMon x xs ys = not (incl xs ys) || incl (remove x xs) (remove x ys) 


propRemoveMapIncl :: (Var -> Var) -> Var -> [Var] -> Bool
propRemoveMapIncl f x xs = incl (remove (f x) (map f xs)) (map f (remove x xs)) 

propRemoveXNotIn :: Var -> [Var] -> Bool
propRemoveXNotIn x xs = x `elem` xs || remove x xs == xs

propRemoveInj :: (Var -> Var) -> Var -> [Var] -> Bool
propRemoveInj f x xs = x `notElem` xs || (not $ injective_on xs f) ||
    remove (f x) (map f xs) == map f (remove x xs)

propRemoveInj2 :: (Var -> Var) -> Var -> [Var] -> Bool
propRemoveInj2 f x xs = (not $ injective_on (x:xs) f) ||
    remove (f x) (map f xs) == map f (remove x xs)

propRemoveIncl :: Var -> [Var] -> Bool
propRemoveIncl x xs = incl (remove x xs) xs

propRemoveCharac :: Var -> [Var] -> Var -> Bool
propRemoveCharac x xs z = (z `elem` remove x xs) == ((z `elem` xs) && (x /= z))
