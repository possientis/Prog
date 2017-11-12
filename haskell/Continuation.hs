import Control.Monad
import Control.Applicative

newtype Cont r a = Cont { runCont :: (a -> r) -> r } 

instance Functor (Cont r) where
    fmap = (<*>) . pure

instance Applicative (Cont r) where
    pure    = return
    (<*>)   = ap

instance Monad (Cont r) where
    return a    = Cont (\k -> k a)
    ma >>= mab  = Cont (\k ->  runCont ma (\a -> runCont (mab a) k)) 

callCC :: ((a -> Cont r b) -> Cont r a) -> Cont r a
callCC f = undefined  



