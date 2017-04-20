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


action'''  = action1 >>= \x -> action2 >>= \y -> action3 x y
action''   = action1 >>= \x -> (action2 >>= \y -> action3 x y)


action = do
    x1 <- action1
    x2 <- action2
    action3 x1 x2  

-- semantics of do slightly more complex than chaining binds,
-- as <- allows for pattern matching which may fail, and failure
-- is handled by fail method of monad

action' = action1 >>= f
  where
    f x1 = do x2 <- action2
              action3 x1 x2
    f _  = fail "..." -- compiler-generated message

-- last line of pattern matching is redundant, but may not be
-- in all cases, if we had things like 'Constructor y1 y2 y3 y4 <- action1'
-- instead of a simple 'x1 <- action1'

-- the signature of the fail method may appear surprising:

-- fail :: Monad m => String -> m a

-- How are we supposed to implement a function returning a 'm a'
-- without being given as argument some element of type a.

-- In the case of return :: a -> m a, it would seem manageable
-- to do something as we are given an argument of type a
--
-- for (>>=) :: m a -> (a -> m b) -> m b

-- well actually
--
-- Maybe : Nothing is of type Maybe a,  forall a
-- []    : [] is of type [a], forall a
-- TODO: understand how fail can have type String -> m a for all a
-- State monad:
-- data M a = M (State -> (State, a))



        
