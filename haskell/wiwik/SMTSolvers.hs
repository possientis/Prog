import Data.Foldable
import Data.SBV


{-
 -        M O N A D
 -  + B U R R I T O
 -  = B A N D A I D
 -}


val :: [SInteger] -> SInteger
val = foldr1 (\d r -> d + 10*r) . reverse


puzzle :: Symbolic SBool
puzzle = do
    ds@[b,u,r,i,t,o,m,n,a,d] <- sequenceA [ sInteger [v] | v <- "buritomnad" ]
    constrain $ allDifferent ds
    for_ ds $ \d -> constrain $ inRange d (0,9)
    pure    $   val [b,u,r,r,i,t,o]
            +   val     [m,o,n,a,d]
           .==  val [b,a,n,d,a,i,d]


main :: IO AllSatResult
main = allSat puzzle

{-
 - Solution #1:
 - b = 4 :: Integer
 - u = 1 :: Integer
 - r = 5 :: Integer
 - i = 9 :: Integer
 - t = 7 :: Integer
 - o = 0 :: Integer
 - m = 8 :: Integer
 - n = 3 :: Integer
 - a = 2 :: Integer
 - d = 6 :: Integer
 - This is the only solution.
 -}


