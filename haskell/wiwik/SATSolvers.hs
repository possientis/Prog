import Picosat

main :: IO Solution
main = do
    solve 
        [   [1,-2, 3]   -- A \/ ~B \/ C
        ,   [2,4,5]     -- B \/  D \/ E
        ,   [4,6]       -- D \/ F
        ]

{-    
    Solution [1,-2,3,4,5,6]
    A = True
    B = False
    C = True
    D = True
    E = True
    F = True
-}


main2 :: IO Solution
main2 = do
    solve
        [   [1,-2]
        ,   [2]
        ]
{- Solution [1,2]
 - A = True and B= True
-}
        
