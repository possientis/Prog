class Graph a where
  source :: a -> a
  target :: a -> a

class Graph a => Category a where
  compose :: a -> a -> Maybe a
  
