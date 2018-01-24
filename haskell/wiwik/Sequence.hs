import Data.Sequence -- optimized for prepend and append

a :: Seq Int
a = fromList [1,2,3]

a0 :: Seq Int
a0 = a |> 4
-- fromList [1,2,3,4]


a1 :: Seq Int
a1 = 0 <| a
-- fromList [0,1,2,3]
