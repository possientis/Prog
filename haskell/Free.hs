{-# LANGUAGE LambdaCase     #-}

import Control.Monad

main :: IO ()
main = runTeletype echo2

data Teletype a
    = Done a
    | WriteLine String (Teletype a)
    | ReadLine (String -> Teletype a)

echo1 :: Teletype ()
echo1 = ReadLine $ \s -> WriteLine s (Done ())

runTeletype :: Teletype a -> IO a
runTeletype = \case
    Done a        -> return a
    WriteLine s k -> putStrLn s >>  runTeletype k
    ReadLine f    -> getLine    >>= runTeletype . f

instance Functor Teletype where
    fmap f = \case
        Done a        -> Done        $ f a
        WriteLine s k -> WriteLine s $ fmap f k
        ReadLine g    -> ReadLine    $ fmap f . g

instance Applicative Teletype where
    pure  = return 
    (<*>) = ap

instance Monad Teletype where
    return = Done
    (>>=) k g = case k of
        Done a        -> g a
        WriteLine s m -> WriteLine s $ m >>= g
        ReadLine f    -> ReadLine    $ flip (>>=) g . f

readLine :: Teletype String
readLine = ReadLine Done

writeLine :: String -> Teletype ()
writeLine s = WriteLine s $ Done ()

echo2 :: Teletype ()
echo2 = do
    writeLine "What is your name:"
    s <- readLine 
    writeLine $ "Hello " ++ s ++ " please to meet you."

