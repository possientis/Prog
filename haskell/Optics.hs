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


     
    
