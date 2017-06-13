module Bar
  ( Bar
  , left
  , right
  ) where

newtype Bar v = Bar { unwrap :: Either v Int } deriving (Eq, Ord)

left :: v -> Bar v
left x = Bar (Left x)

right :: Int -> Bar v
right n = Bar (Right n)

instance (Show v) => Show (Bar v) where
  show (Bar (Left x))   = show x
  show (Bar (Right n))  = show n
