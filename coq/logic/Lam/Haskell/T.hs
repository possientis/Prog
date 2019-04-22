module  Lam.Haskell.T
    (   T   (..)
    )   where

import Test.QuickCheck

data T v
    = Var v
    | App (T v) (T v)
    | Lam v (T v)

-- TODO : proper parsing and pretty printing 
instance (Show v) => Show (T v) where
    show (Var v)    = show v
    show (App t s)  = "("   ++ show t ++ " "    ++ show s ++ ")"
    show (Lam v t)  = "(\\" ++ show v ++ " -> " ++ show t ++ ")"

-- TODO : something better than this
instance (Arbitrary v) => Arbitrary (T v) where
    arbitrary = frequency 
        [ (4, Var <$> arbitrary)
        , (3, App <$> arbitrary <*> arbitrary)
        , (8, Lam <$> arbitrary <*> arbitrary)
        ]

