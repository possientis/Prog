{-# LANGUAGE Rank2Types #-}

-- without type signature, GHC will attempt to unify Bool and Char
-- which will fail. You need a type signature. However, the type
-- involved does not have quatification at the top level (Rank 1)
-- but at the second level (Rank 2)
-- higher rank types cannot be inferred.

higherRank :: (forall a. a -> a) -> (Bool, Char)
higherRank f = (f True, f 'x')
