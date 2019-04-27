{-# LANGUAGE DeriveFunctor #-}

module  Fol.Haskell.P
    (   P   (..)
    )   where

import Test.QuickCheck

data P v
    = Bot
    | Elem v v 
    | Imp (P v) (P v)
    | All v (P v)
    deriving (Functor, Eq)



-- TODO : proper parsing and pretty printing 
instance (Show v) => Show (P v) where
    show Bot        = "bot"
    show (Elem x y) = show x ++ ":" ++ show y 
    show (Imp p q)  = "(" ++ show p ++ " -> " ++ show q ++ ")"
    show (All x p)  = "(A" ++ show x ++ "." ++ show p ++ ")"


instance (Arbitrary v) => Arbitrary (P v) where
    arbitrary = frequency
        [ (3, return Bot)
        , (4, Elem <$> arbitrary <*> arbitrary)
        , (3, Imp  <$> arbitrary <*> arbitrary)
        , (8, All  <$> arbitrary <*> arbitrary)
        ]
