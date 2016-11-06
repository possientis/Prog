newtype M s a = M { runM :: s -> (a, s) }

state :: (s -> (a, s)) -> M s a
state = M

get :: M s s
get = state $ \s -> (s, s)

put :: s -> M s ()
put s = state $ \t -> ((), s)


instance Monad (M s) where
  return x = state $ \s -> (x, s)
  m >>= f  = state $ \s -> let (x, t) = runM m s in runM (f x) t 

-- IO (M s a)
-- M s (IO a)

newtype M1 s a = M1(IO (M s a)) -- essentially IO (s -> (a, s))
newtype M2 s a = M2(M s (IO a)) -- essentially s -> (IO a, s)


i1 :: M1 s a -> IO (s -> (a, s))
i1 (M1 m) = m >>= return . runM     -- return :: s -> (a, s) -> IO (s -> (a, s))

j1 :: IO (s -> (a, s)) -> M1 s a 
j1 m = M1 $ m >>= return . state    -- return :: M s a -> IO (M s a)

{-
 
i1 . j1 m = i1 (j1 m)
          = i1 (M1 (m >>= return . state))
          = i1 (M1 k) where k = m >>= return  . state 
          = k >>= return . runM
          = (m >>= return . state) >>= return . runM
          = m >>= (return . run M . state) 
          = m >>= return
          = m

j1 . i1 (M1 m)  = j1 ( i1 (M1 m))
                = j1 (m >>= return . runM)
                = M1 (k >>= return . state) where k = m >>= return . runM
                = M1 ((m >>= return . runM) >>= return . state)
                = M1 (m >>= return . state . runM)
                = M1 (m >>= return)
                = M1 m
-}

newtype N1 s a = IO (s -> (a, s)) -- same as M1 s a

i2 :: M2 s a -> s -> (IO a , s)
i2 (M2 m) = runM m 

j2 :: (s -> (IO a, s)) -> M2 s a 
j2 = M2 . state 

{-

i2 . j2 f = i2 (j2 (f))
          = i2 (M2 (state f))
          = i2 (M2 m) where m = state f
          = runM m
          = runM . state f
          = f

j2 . i2 (M2 m)  = j2 (runM m)
                = M2 . state . runM m
                = M2 m

-}

i3 :: (s -> (IO a, s)) -> s -> IO (a, s)
i3 f s = do
  let (io, t) = f s
  x <- io
  return (x, t)

-- it has to be  s -> m (a, s)









 









    
          



    
    
  




