{-# LANGUAGE ViewPatterns #-}

import Data.Sequence

{-

empty :: Seq a

(<|) :: a -> Seq a -> Seq a
(|>) :: Seq a -> a -> Seq a

data ViewL a = EmptyL | a :< (Seq a)
data ViewR a = EmptyR | (Seq a) :> a

viewl :: Seq a -> ViewL a
viewr :: Seq a -> ViewR a 
-}

ex0 = empty :: Seq Int

ex1 = 0 <| ex0

ex2 = 1 <| ex1

ex3 = ex2 |> 2   -- fromList [1,0,2]


main :: IO ()
main = do
    print ex3
    print $ uncons ex3

-- can do better with ViewPatterns extension
uncons' :: Seq a -> Maybe (a, Seq a)
uncons' xs = case viewl xs of
    x :< xs'    -> Just (x, xs')
    EmptyL      -> Nothing

{- LANGUAGE ViewPatterns #-}
uncons :: Seq a -> Maybe (a, Seq a)
uncons (viewl -> x :< xs )  = Just (x, xs)
uncons _                    = Nothing








