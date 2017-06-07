data A  = A Int A
data B = B (() -> (Int, B))

from :: Int -> A
from n = A n $ from (n+1)

integers :: A
integers = from 0

head :: A -> Int
head (A n ns) = n

toList :: A -> [Int]
toList (A n ns) = n : toList ns


toB :: A -> B
toB (A n ns) = B (\_ -> (n, toB ns))

toA :: B -> A
toA (B f) = A ((fst . f) ()) $ toA ((snd . f) ())

integers' = toA $ toB integers



main :: IO ()
main = do
  putStrLn $ show $ take 10 $ toList integers'
