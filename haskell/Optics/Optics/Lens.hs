module  Optics.Lens
    (   Lens    (..)
    )   where


data  Lens a b s t 
    = Lens 
    { view :: s -> a
    , update :: (b,s) -> t 
    }





