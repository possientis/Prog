data Term = Con Int | Add Term Term


eval :: Monad m => Term -> m Int
eval (Con a)    = return a
eval (Add t u)  = do
  a <- eval t
  b <- eval u
  return (a + b)


eval' :: Monad m => Term -> m Int
eval' (Con a)   = return a
eval' (Add t u) = 
  eval t >>= \a -> 
    eval u >>= \b -> 
      return (a + b)
  
liftM :: Monad m => (a -> b) -> m a -> m b
liftM f = (>>= return . f)

join :: Monad m => m (m a) -> m a
join = (>>= id)

{-
liftM id  = (>>= return . id)
          = (>>= return)
          = id
-}          

{-
liftM (f.g) m = (m >>= return . (f.g))
              = (m >>= ((return . f) . g))
              = (m >>= (return . g)) >>= (return . f) 
              = (liftM g m) >>= (return . f)
              = liftM f (liftM g m)
              = ((liftM f) . (liftM g)) m
-}

{-

(liftM f) . return x  = (>>= return . f) . return x  
                      = (return x) >>= (return . f)
                      = (return . f) x
-}

{-

(liftM f) . join m  = (>>= return . f) . (>>= id) m 
                    = (>>= return . f) (m >>= id)
                    = (m >>= id) >>= return . f
                    = ... 
-}
                    
                    





