module  Optics.Prism
    (   Prism    (..)
    )   where

data  Prism s t a b 
    = Prism 
    { match :: s -> Either t a
    , build :: b -> t 
    }



