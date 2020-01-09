module  Optics.Optic
    (   Optic
    )   where


type Optic p s t a b = p a b -> p s t

