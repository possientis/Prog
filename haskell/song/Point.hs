module  Point
    (   Point
    ,   point
    )   where

data Point a = Point
    { _a  :: a
    , _b  :: a
    , _xy :: Maybe (a,a)    -- Nothing is point at infinity
    }


point :: (Eq a, Num a) => a -> a -> Maybe (a,a) -> Point a
point a b z 
    | Just (x,y) <-z
    , y * y /= x * x * x + a * x + b    = error "point: not on curve"
    | otherwise                         = Point a b z                             

instance (Eq a) => Eq (Point a) where
    (==) (Point a b z) (Point a' b' z') = a == a' && b == b' && z == z'


