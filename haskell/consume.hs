-- another parsing exercise
import Control.Monad

digit :: Int -> String -> Maybe Int
digit i s | i > 9 || i < 0  = Nothing
          | otherwise       = do
  let (c:_) = s
  if read [c] == i then Just i else Nothing 

-- consumes a binary character in the input
binChar :: String -> Maybe Int
binChar s = digit 0 s `mplus` digit 1 s


