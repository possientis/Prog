{-# LANGUAGE RankNTypes         #-}  
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE TypeOperators      #-}

type f ~> g = forall a . f a -> g a


data F a = F (a,a)
    deriving (Functor)

data G a = G [a]
    deriving (Functor)

-- natural transformation from F to G
alpha :: F ~> G 
alpha (F (x,y)) = G [x,y]


-- natural transformation from [] to Maybe
safeHead :: [] ~> Maybe
safeHead [] = Nothing
safeHead (a:_) = Just a

nothing :: [] ~> Maybe
nothing _ = Nothing




