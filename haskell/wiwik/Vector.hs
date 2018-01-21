import Prelude hiding (map,sum)
import Data.Vector.Unboxed

norm :: Vector Double -> Double
norm = sqrt . sum . map (\x -> x*x)


ex1 :: Double
ex1 = norm $ iterateN 100000000 (+1) 0.0


main :: IO ()
main = do
    print $ ex1
