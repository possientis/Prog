import qualified Data.Sequence as Seq
import qualified Data.Foldable as Foldable

-- so we don't have to qualify those names with 'Seq'
import Data.Sequence ((><), (<|), (|>)) 

test1 = Seq.empty             -- fromList []

test2 = Seq.singleton 1       -- fromList [1]  

test3 = Seq.fromList [1,2,3]  -- fromList [1,2,3]

-- <| adding to the left operation is constant time
test4 = 1 <| Seq.singleton 2  -- fromList [1,2]

-- |> adding to the right operation is constant time
test5 = Seq.singleton 1 |> 2  -- fromList [1,2]

left1 = Seq.fromList [1,3,3]
right1 = Seq.fromList [7,1]

-- appending O(log(n)) where n is min of the two sizes
test6 = left1 >< right1 -- fromList [1,3,3,7,1]

test7 = Foldable.toList (Seq.fromList [1,2,3])  -- [1,2,3]

test8 = Foldable.foldl' (+) 0 (Seq.fromList [1,2,3])  -- 6




