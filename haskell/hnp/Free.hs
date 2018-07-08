import Control.Monad

data Free f a = Pure a | Free (f (Free f a))

instance Functor f => Functor (Free f) where
    fmap                    = liftM

instance Functor f => Applicative (Free f) where
    pure                    = return
    (<*>)                   = ap

instance Functor f => Monad (Free f) where
    return                  = Pure
    (>>=) (Pure a) g        = g a
    (>>=) (Free k) g        = Free $ fmap (>>= g) k 


data TeletypeF next
    = PrintLine String next
    | ReadLine (String -> next)

instance Functor TeletypeF where
    fmap f (PrintLine s a) = PrintLine s (f a)
    fmap f (ReadLine g)    = ReadLine (f . g)

type Teletype = Free TeletypeF

printLine :: String -> Teletype ()
printLine s = Free (PrintLine s (Pure ()))

readLine :: Teletype String
readLine = Free (ReadLine (\s -> Pure s))

echo :: Teletype ()
echo = readLine >>= printLine

interpret :: Teletype a -> IO a
interpret (Pure a) = return a
interpret (Free (PrintLine s next)) = putStrLn s >> interpret next
interpret (Free (ReadLine g))       = getLine >>= interpret . g 


main :: IO ()
main = interpret echo



