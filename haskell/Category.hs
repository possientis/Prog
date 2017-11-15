{-# LANGUAGE NoImplicitPrelude #-}

import qualified Prelude

class Category cat where
    id  :: cat a a
    (.) :: cat b c -> cat a b -> cat a c


instance Category (->) where
    id  = Prelude.id
    (.) = (Prelude..)


(<<<) :: Category cat => cat b c -> cat a b -> cat a c
(<<<) = (.)


(>>>) :: Category cat => cat a b -> cat b c -> cat a c
f >>> g = g . f


class Category cat => Arrow cat where
    arr     :: (a -> b) -> cat a b
    first   :: cat a b -> cat (a,d) (b,d)
    second  :: cat a b -> cat (d,a) (d,b)
    (***)   :: cat a b -> cat a' b' -> cat (a,a') (b,b')
    (&&&)   :: cat a b -> cat a  b' -> cat a (b,b') 


instance Arrow (->) where
    arr f = f
    first f = f *** id
    second f = id *** f
    (***) f g ~(x,y) = (f x , g y)
    





  
