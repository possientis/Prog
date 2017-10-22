module  MonadWriter  
    (   Writer      (..)
    ,   tell
    ,   execWriter
    )   where

import Data.Monoid
import Control.Monad (ap)


newtype Writer w a = Writer { runWriter :: (a,w) }

instance Monoid w => Functor (Writer w) where
    fmap f u = pure f <*> u


instance Monoid w => Applicative (Writer w) where
    pure  = return
    (<*>) = ap 

instance Monoid w =>  Monad (Writer w) where
    return a = Writer (a,mempty)
    m >>= k  = Writer $ let (a,w) = runWriter m
        in let (b,w') = runWriter (k a)
            in (b, w <> w')

tell :: w -> Writer w ()
tell w = Writer ((),w)


execWriter :: Writer w a -> w
execWriter = snd . runWriter








