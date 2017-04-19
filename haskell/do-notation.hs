main1 = putStr "Hello"  >>
        putStr " "      >>
        putStr "world!" >>
        putStr "\n" 

main2 = do  putStr "Hello"  
            putStr " "      
            putStr "world!" 
            putStr "\n" 

action1 = Just 1    
action2 = Just 2          
action3 x y = Just $ x + y  


action  = action1 >>= \x -> action2 >>= \y -> action3 x y
action' = action1 >>= \x -> (action2 >>= \y -> action3 x y)



        
