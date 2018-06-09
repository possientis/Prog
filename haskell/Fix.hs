import Data.Default

newtype Fix a = MkFix { unFix :: Fix a -> a }


ex1 :: (Default a) => Fix a
ex1 = MkFix (const def)

ex2 :: Fix Int
ex2 = MkFix (const 0)

f1 :: Fix Int -> Int
f1 (MkFix f) = case f ex2 of
    0   -> 23
    _   -> 46 

ex3 :: Fix Int
ex3 = MkFix f1

apply :: Fix a -> Fix a -> a
apply = unFix

part :: (a -> a) -> Fix a
part f = MkFix (\x -> f (apply x x))

fix :: (a -> a) -> a 
fix f = apply (part f) (part f)


{-

fix f
apply (part f) (part f)
apply (MkFix (\x -> f (apply x x)) (part f))
(\x -> f (apply x x)) (part f)
f (apply (part f) (part f))
f (fix f)

-}


f2 :: Double -> Double
f2 x = x * x

main :: IO ()
main = do
    print $ apply ex2 ex2
    print $ apply ex2 ex3
    print $ apply ex3 ex2
    print $ apply ex3 ex2 


