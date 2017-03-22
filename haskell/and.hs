-- and is a fold

import Prelude hiding (and)

and :: Foldable t => t Bool -> Bool
and = foldr (&&) True

main :: IO ()
main = do 
  putStrLn $ show $ and []
  putStrLn $ show $ and [True, True, False, (error "don't worry") , True]
  putStrLn $ show $ and [True, True, True, True, True]
  putStrLn $ show $ and' [True, True, False, (error "don't worry") , True]


and' :: [Bool] -> Bool
and' []     = True
and' (x:xs) = x && (and' xs)  -- above works because && does not 
                              -- depend on rhs when lhs False 

-- if && was incorrectly implemented by forcing both lhs and rhs
-- things would go wrong above with 'error'
(<&>) :: Bool -> Bool -> Bool
x<&>y = seq y (x && y)

