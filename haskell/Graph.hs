import Set

class IGraph a where
  source :: a -> a
  target :: a -> a
