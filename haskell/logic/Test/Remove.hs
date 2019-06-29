module  Test.Remove
    (   specRemove
    )   where

import  Test.Hspec
import  Test.QuickCheck

import Remove
import Include
import Variable (Var)


specRemove :: Spec
specRemove = describe "Testing properties for remove..." $ 
    sequence_ specsRemove

specsRemove :: [Spec]
specsRemove  = [ testRemoveStill
               , testRemoveMon
               , testRemoveMap
               ]


testRemoveStill :: Spec
testRemoveStill = it "Checked remove vs elem property" $
    property $ propRemoveStill

testRemoveMon :: Spec
testRemoveMon = it "Checked remove monotone property" $
    property $ propRemoveMon

testRemoveMap :: Spec
testRemoveMap = it "Checked remove map property" $ 
    property $ propRemoveMap

propRemoveStill :: Var -> Var -> [Var] -> Bool
propRemoveStill x y xs = x == y || y `notElem` xs || y `elem` (remove x xs) 


propRemoveMon :: Var -> [Var] -> [Var] -> Bool
propRemoveMon x xs ys = not (incl xs ys) || incl (remove x xs) (remove x ys) 


propRemoveMap :: (Var -> Var) -> Var -> [Var] -> Bool
propRemoveMap f x xs = incl (remove (f x) (map f xs)) (map f (remove x xs)) 



