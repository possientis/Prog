import qualified Data.HashSet as S
import qualified Data.HashMap.Lazy as M


ex1 :: M.HashMap Int Char
ex1 = M.fromList $ zip [1..10] ['a'..]


ex2 :: S.HashSet Int
ex2 = S.fromList [1..10]


main :: IO ()
main = do
    print ex1
    print ex2




