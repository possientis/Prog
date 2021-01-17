import Control.Monad

data Teletype k
    = Done k
    | WriteLine String (Teletype k)
    | ReadLine (String -> Teletype k)

echo1 :: Teletype ()
echo1 = ReadLine $ \msg -> 
        WriteLine msg
      $ Done ()

instance Functor Teletype where
    fmap f (Done k) = Done (f k)
    fmap f (WriteLine msg t) = WriteLine msg (fmap f t)
    fmap f (ReadLine g) = ReadLine (fmap f . g)

instance Applicative Teletype where
    pure  = return
    (<*>) = ap

instance Monad Teletype where
    return = Done
    Done          k >>= f = f k
    WriteLine msg k >>= f = WriteLine msg $ k >>= f
    ReadLine      k >>= f = ReadLine $ \s -> k s >>= f
    
echo2 :: Teletype ()
echo2 = do
    msg <- ReadLine Done
    WriteLine msg $ Done ()

runTeletypeInIO :: Teletype a -> IO a
runTeletypeInIO (Done a) = pure a
runTeletypeInIO (WriteLine msg k) = do
    putStrLn msg
    runTeletypeInIO k 
runTeletypeInIO (ReadLine k) = do
    s <- getLine
    runTeletypeInIO $ k s

main :: IO ()
main = runTeletypeInIO echo2

-- min 16:00
