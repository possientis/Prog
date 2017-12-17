{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}

import Data.Char
import Data.Text
import Data.Monoid
import Data.MList
import Control.Applicative
import Data.MonoTraversable

bs :: Text
bs = "Hello Haskell."

shift :: Text
shift = omap (chr . (+1) . ord) bs

backwards :: [Char]
backwards = ofoldl' (flip (:)) "" bs


data MyMonoType = MNil | MCons Int MyMonoType deriving Show

type instance Element MyMonoType = Int

instance MonoFunctor MyMonoType where
    omap f MNil = MNil
    omap f (MCons x xs) = f x `MCons` omap f xs


instance MonoFoldable MyMonoType where
    ofoldMap f  = ofoldr (mappend . f) mempty
    ofoldr      = mfoldr
    ofoldl'     = mfoldl'
    ofoldr1Ex f = ofoldr1Ex f . mtoList
    ofoldl1Ex' f= ofoldl1Ex' f . mtoList 
