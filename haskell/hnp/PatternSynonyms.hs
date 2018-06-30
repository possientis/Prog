
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}


import Data.Sequence (Seq, (|>), (<|))
import qualified Data.Sequence as Seq

{- LANGUAGE PatternSynonyms -}
pattern Empty :: Seq a
pattern Empty <- (Seq.viewl -> Seq.EmptyL)

pattern (:<) :: a -> Seq a -> Seq a
pattern x :< xs <- (Seq.viewl -> x Seq.:< xs)

pattern (:>) :: Seq a -> a -> Seq a 
pattern xs :> x <- (Seq.viewr -> xs Seq.:> x)


-- This allows writing uncons in a very natural style

uncons :: Seq a -> Maybe (a, Seq a)
uncons (x :< xs) = Just (x,xs)
uncons Empty     = Nothing

vec :: Seq Int
vec = (-2) <| (-1) <| (Seq.empty |> 0 |> 1 |> 2)

main :: IO ()
main = print $ uncons vec
