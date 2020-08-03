{-# LANGUAGE LambdaCase         #-}

module Lam.BetaValid
    (   betaValid_
    ,   betaValid
    )   where

import Lam.Free
import Lam.Syntax

import List.Difference

betaValid_ :: (Eq v) => (v -> T v) -> [v] -> T v -> Bool
betaValid_ f xs = \case
    Var _       -> True
    App t1 t2   -> betaValid_ f xs t1 && betaValid_ f xs t2
    Lam x t1    -> betaValid_ f (x : xs) t1 &&
        all (\u -> x `notElem` free (f u)) (free (Lam x t1) \\ xs)

betaValid :: (Eq v) => (v -> T v) -> T v -> Bool
betaValid f t = betaValid_ f [] t

