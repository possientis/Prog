{-# LANGUAGE ScopedTypeVariables #-}

import Data.Monoid


bar :: (Monoid b, Monoid c) => (a, b, c) -> (b, c) -> (a, b, c)
bar (a, b, c) (b', c') = (a, b <> b', c <> c')
    
{- LANGUAGE ScopedTypeVariables -}
foo :: forall a b c. (Monoid b, Monoid c) => (a, b, c) -> (b, c) ->  (a, b, c)
foo (a, b, c) (b', c') = (a :: a, b'', c'') 
    where (b'', c'') = (b <> b', c <> c') :: (b, c)
