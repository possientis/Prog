{-# LANGUAGE PolyKinds #-}

-- with PolyKinds extension
-- T :: (k -> *) -> k -> *
-- without PolyKinds extension
-- T :: (* -> *) -> * -> *

data T f a = MkT (f a)
