module  Test.Lam.BetaValid
    (   specBetaValid
    )   where


import Test.Hspec
import Test.QuickCheck  hiding ((===))

import Formula
import Variable     (Var)

import List.Equiv
import List.Include
import List.Coincide
import List.Intersect
import List.Difference

import Lam.Subst
import Lam.Syntax
import Lam.Replace
import Lam.BetaValid

specBetaValid :: Spec
specBetaValid = describe "Testing non-polymorphic properties of BetaValid..." $ do
    testBetaValidVarGen
    testBetaValidVar
    testBetaValidAppGen
    testBetaValidApp
    testBetaValidLamGen
    testBetaValidLam
    testBetaValidIncl
    testBetaValidFreeGen
    testBetaValidFree
    testBetaValidCoincideGen
    testBetaValidCoincide
    testBetaValidSubstGen
    testBetaValidSubst
    testBetaValidSupport
    testBetaValidInterVarGen
    testBetaValidInterVar
    testBetaValidReplaceTGen
    testBetaValidReplaceT

testBetaValidVarGen :: Spec
testBetaValidVarGen = it "Checked generic beta validity for variables" $
    property propBetaValidVarGen

testBetaValidVar :: Spec
testBetaValidVar = it "Checked beta validity for variables" $
    property propBetaValidVar

testBetaValidAppGen :: Spec
testBetaValidAppGen = it "Checked generic beta validity for applications" $
    property propBetaValidAppGen

testBetaValidApp :: Spec
testBetaValidApp = it "Checked beta validity for applications" $
    property propBetaValidApp

testBetaValidLamGen :: Spec
testBetaValidLamGen = it "Checked generic beta validity for lambda abstraction" $
    property propBetaValidLamGen

testBetaValidLam :: Spec
testBetaValidLam = it "Checked beta validity for lambda abstraction" $
    property propBetaValidLam

testBetaValidIncl :: Spec
testBetaValidIncl = it "Checked beta validity inclusion property" $ do
    property propBetaValidIncl

testBetaValidFreeGen :: Spec
testBetaValidFreeGen = it "Checked generic beta validity free property" $ do
    property propBetaValidFreeGen

testBetaValidFree :: Spec
testBetaValidFree = it "Checked beta validity free property" $ do
    property propBetaValidFree

testBetaValidCoincideGen :: Spec
testBetaValidCoincideGen = it "Checked generic beta validity coincide property"$ do
    property propBetaValidCoincideGen

testBetaValidCoincide :: Spec
testBetaValidCoincide = it "Checked beta validity coincide property" $ do
    property propBetaValidCoincide

testBetaValidSubstGen :: Spec
testBetaValidSubstGen = it "Checked generic beta validity subst property" $ do
    property propBetaValidSubstGen

testBetaValidSubst :: Spec
testBetaValidSubst = it "Checked beta validity subst property" $ do
    property propBetaValidSubst

testBetaValidSupport :: Spec
testBetaValidSupport = it "Checked beta validity support property" $ do
    property propBetaValidSupport

testBetaValidInterVarGen :: Spec
testBetaValidInterVarGen = it "Checked gen beta validity inter var property" $ do
    property propBetaValidInterVarGen

testBetaValidInterVar :: Spec
testBetaValidInterVar = it "Checked beta validity inter var gen property" $ do
    property propBetaValidInterVar

testBetaValidReplaceTGen :: Spec
testBetaValidReplaceTGen = it "Checked beta validity replaceT gen property" $ do
    property propBetaValidReplaceTGen

testBetaValidReplaceT :: Spec
testBetaValidReplaceT = it "Checked beta validity replaceT property" $ do
    property propBetaValidReplaceT

propBetaValidVarGen :: (Var -> T Var) -> Var -> [Var] -> Bool
propBetaValidVarGen f x xs = betaValid_ f xs (Var x)

propBetaValidVar :: (Var -> T Var) -> Var -> Bool
propBetaValidVar f x = betaValid f (Var x)

propBetaValidAppGen :: (Var -> T Var) -> T Var -> T Var -> [Var] -> Bool
propBetaValidAppGen f t1 t2 xs = 
    betaValid_ f xs (App t1 t2) == (betaValid_ f xs t1 && betaValid_ f xs t2)

propBetaValidApp :: (Var -> T Var) -> T Var -> T Var -> Bool
propBetaValidApp f t1 t2 = 
    betaValid f (App t1 t2) == (betaValid f t1 && betaValid f t2)

propBetaValidLamGen :: (Var -> T Var) -> T Var -> Var -> [Var] -> Bool
propBetaValidLamGen f t1 x xs = betaValid_ f xs (Lam x t1) == 
    ((betaValid_ f (x : xs) t1) && all p (free (Lam x t1) \\ xs))
    where
        p :: Var -> Bool
        p u = x `notElem` free (f u)

propBetaValidLam :: (Var -> T Var) -> T Var -> Var -> Bool
propBetaValidLam f t1 x = betaValid f (Lam x t1) == 
    ((betaValid_ f [x] t1) && all p (free (Lam x t1)))
    where
        p :: Var -> Bool
        p u = x `notElem` free (f u)

propBetaValidIncl :: (Var -> T Var) -> T Var -> [Var] -> [Var] -> Bool
propBetaValidIncl f t xs ys = not (xs <== ys) ||
   not (betaValid_ f xs t) || betaValid_ f ys t 

propBetaValidFreeGen :: (Var -> T Var) -> T Var -> [Var] -> Bool
propBetaValidFreeGen f t xs = not (betaValid_ f xs t) ||
    (free (subst_ f xs t)===(free t /\ xs) ++ concatMap (free . f)(free t \\ xs))

propBetaValidFree :: (Var -> T Var) -> T Var -> Bool
propBetaValidFree f t = not (betaValid f t) ||
    (free (subst f t) === concatMap (free . f) (free t))

propBetaValidCoincideGen 
    :: (Var -> T Var) 
    -> (Var -> T Var) 
    -> T Var 
    -> [Var] 
    -> Bool
propBetaValidCoincideGen f g t xs = not (coincide (free t \\ xs) f g) ||
    betaValid_ f xs t == betaValid_ g xs t

propBetaValidCoincide
    :: (Var -> T Var) 
    -> (Var -> T Var) 
    -> T Var 
    -> Bool
propBetaValidCoincide f g t = not (coincide (free t) f g) ||
    betaValid f t == betaValid g t

propBetaValidSubstGen
    :: (Var -> T Var) 
    -> (Var -> T Var) 
    -> T Var 
    -> [Var]
    -> Bool
propBetaValidSubstGen f g t xs = subst_ f xs t /= subst_ g xs t || 
    betaValid_ f xs t == betaValid_ g xs t

propBetaValidSubst
    :: (Var -> T Var) 
    -> (Var -> T Var) 
    -> T Var 
    -> Bool
propBetaValidSubst f g t = subst f t /= subst g t || 
    betaValid f t == betaValid g t

propBetaValidSupport
    :: (Var -> T Var) 
    -> T Var 
    -> [Var]
    -> [Var]
    -> Bool
propBetaValidSupport f t xs ys = (free t /\ xs) /== (free t /\ ys) || 
    betaValid_ f xs t == betaValid_ f ys t

propBetaValidInterVarGen
    :: (Var -> T Var) 
    -> T Var 
    -> [Var]
    -> Bool
propBetaValidInterVarGen f t xs = 
    (var t /\ concatMap (\u -> free (f u) \\ [u]) (free t \\ xs)) /= [] ||
        betaValid_ f xs t

propBetaValidInterVar :: (Var -> T Var) -> T Var -> Bool
propBetaValidInterVar f t = 
    (var t /\ concatMap (\u -> free (f u) \\ [u]) (free t)) /= [] ||
        betaValid f t

propBetaValidReplaceTGen
    :: T Var
    -> T Var
    -> [Var] 
    -> Var
    -> Bool
propBetaValidReplaceTGen s t xs x =
    ((x `elem` (free t \\ xs)) && (not $ (var t /\ free s) <== [x])) ||
        betaValid_ (s <-: x) xs t

propBetaValidReplaceT :: T Var -> T Var -> Var -> Bool
propBetaValidReplaceT s t x =
    ((x `elem` free t) && (not $ (var t /\ free s) <== [x])) ||
        betaValid (s <-: x) t



