-- {-# LANGUAGE DeriveFunctor #-}

import Control.Monad.Free
import Control.Monad

data TeletypeF next
    = PrintLine String next
    | ReadLine (String -> next)
    {- deriving Functor -}

instance Functor TeletypeF where
    fmap f (PrintLine s a) = PrintLine s (f a)
    fmap f (ReadLine g)    = ReadLine (f . g)

-- free monad over functor TeletypeF
type Teletype = Free TeletypeF

printLine :: String -> Teletype ()
printLine s = liftF (PrintLine s ())


readLine :: Teletype String
readLine = liftF (ReadLine id)


echo :: Teletype ()
echo = readLine >>= printLine

mockingbird :: Teletype ()
mockingbird = forever echo

interpretTeletype :: Teletype a -> IO a
interpretTeletype = foldFree run where
    run :: TeletypeF a -> IO a
    run (PrintLine s x) = putStrLn s *>  return x
    run (ReadLine f)    = fmap f getLine


main :: IO ()
main = interpretTeletype mockingbird
