module  Optics.Prism
    (   Prism    (..)
    )   where

data  Prism a b s t
    = Prism 
    { match :: s -> Either t a
    , build :: b -> t 
    }



