data  Lens s t a b 
    = Lens 
    { view :: s -> a
    , update :: (b,s) -> t 
    }

data  Prism s t a b 
    = Prism 
    { match :: s -> Either t a
    , build :: b -> t 
    }

data  Adapter s t a b 
    = Adapter 
    { from :: s -> a
    , to   :: b -> t 
    }
    
data State s a = State { run :: s -> (a, s) }

data Tree a = Empty | Node (Tree a) a (Tree a)


instance Functor (State s) where 
    fmap f k = State $ \s -> let (a,s') = run k s in (f a, s')

instance Applicative (State s) where
    pure x  = State $ \s -> (x, s)
    m <*> k = State $ \s -> 
        let (f,s') = run m s in
            let (x,s'') = run k s' in
                (f x, s'') 

p1 :: Lens (a,c) (b,c) a b
p1  = Lens view_ update_ where
    view_ (x,_) = x
    update_ (x',(_,c)) = (x',c)

sign :: Lens Integer Integer Bool Bool
sign  = Lens view_ update_ where
    view_ n = (n >= 0)
    update_ (b,n) = if b then abs n else -(abs n)

the :: Prism (Maybe a) (Maybe b) a b
the  = Prism match_ build_ where
    match_ (Just x) = Right x
    match_ Nothing  = Left Nothing
    build_ x        = Just x


whole :: Prism Double Double Integer Integer
whole  = Prism match_ build_ where
    match_ x
        | f == 0    = Right n
        | otherwise = Left x
        where (n,f) = properFraction x
    build_ = fromIntegral

p11 :: Lens ((a,c),d) ((b,c),d) a b
p11  = Lens view_ update_ where
    Lens v u = p1
    view_   = v . v
    update_ (x',xyz) = u (xy', xyz) where
        xy' = u (x', xy)
        xy  = v  xyz

flatten :: Adapter ((a,b),c) ((a',b'),c') (a,b,c) (a',b',c')
flatten  = Adapter from_ to_ where
    from_ ((x,y),z) = (x,y,z)
    to_ (x,y,z)   = ((x,y),z)

inc :: Bool -> State Integer Bool
inc b = State $ \s -> (b, s + 1)


inorder :: (Applicative f) => (a -> f b) -> Tree a -> f (Tree b)
inorder _ Empty = pure Empty
inorder g (Node lt x rt) = pure Node <*> inorder g lt <*> g x <*> inorder g rt

     
countOdd :: Integer -> State Integer Bool
countOdd n = if even n then pure False else inc True    



