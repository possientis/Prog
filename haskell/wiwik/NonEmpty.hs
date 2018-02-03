import Data.List.NonEmpty
import Prelude hiding (head, tail, foldl1)
import Data.Foldable (foldl1)

a :: NonEmpty Integer
a = fromList [1,2,3]

b :: NonEmpty Integer
b = 1 :| [1,2]

c :: NonEmpty Integer
c = fromList [] -- exception when evaluated

d :: Integer
d = foldl1 (+) $ fromList [1..100]


main :: IO ()
main = do
    print d
