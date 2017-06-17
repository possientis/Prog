
module Bar
  ( Bar
  , isInt
  , isV
  , left
  , right
  ) where

newtype Bar v = Bar { unwrap :: Either v Int } deriving (Eq, Ord)

left :: v -> Bar v
left x = Bar (Left x)

right :: Int -> Bar v
right n = Bar (Right n)

isInt :: Bar v -> Bool
isInt (Bar (Left _))  = False
isInt (Bar (Right _)) = True

isV :: Bar v -> Bool
isV (Bar (Left _))  = True
isV (Bar (Right _)) = False


instance (Show v) => Show (Bar v) where
  show (Bar (Left x))   = show x
  show (Bar (Right n))  = show n
