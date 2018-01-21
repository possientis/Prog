import Data.Set

set :: Set Integer
set = fromList [1..1000]

isIn :: Integer -> Bool
isIn n = member n set
