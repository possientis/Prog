{-# LANGUAGE ExistentialQuantification  #-}

--import Data.Profunctor

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

-- Adapters are lenses
toLense :: Adapter s t a b -> Lens s t a b
toLense x = Lens view_ update_ where
    view_ = from x
    update_ = to x . fst 
    
-- Adapters are prisms
toPrism :: Adapter s t a b -> Prism s t a b
toPrism x = Prism match_ build_ where
    match_ = Right . from x
    build_ = to x


