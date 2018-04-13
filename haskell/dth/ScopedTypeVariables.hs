{-# LANGUAGE ScopedTypeVariables #-}

import Prelude hiding (foldl)


foldl :: forall a b. (b -> a -> b) -> b -> [a] -> b
foldl op z xs  = go z xs where
  go :: b -> [a] -> b -- a b would not be in scope without 'forall a b'
  go z []      = z
  go z (x:xs)  = go (op z x) xs




