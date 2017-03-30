data List1 a = Nil1 | Con1 a (List1 a) deriving Show

-- need to use -xGADTs option for this syntax to be accepted
data List2 a where
  Nil2 :: List2 a
  Con2 :: a -> List2 a -> List2 a
  deriving Show

