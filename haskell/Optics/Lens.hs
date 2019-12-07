module  Optics.Lens
    (   Lens    (..)
    )   where


data  Lens s t a b 
    = Lens 
    { view :: s -> a
    , update :: (b,s) -> t 
    }


