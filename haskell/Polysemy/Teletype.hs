{-# LANGUAGE LambdaCase     #-}

module  Teletype
    (   Teletype    (..)
    ,   readLine
    ,   writeLine
    ,   runTeletype
    ,   runTeletypePurely
    )   where 

import Control.Monad

data Teletype a
    = Done a
    | WriteLine String (Teletype a)
    | ReadLine (String -> Teletype a)

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

runTeletype :: Teletype a -> IO a
runTeletype = \case
    Done a        -> return a
    WriteLine s k -> putStrLn s >>  runTeletype k
    ReadLine f    -> getLine    >>= runTeletype . f

runTeletypePurely :: [String] -> Teletype a -> ([String], a)
runTeletypePurely xs = \case
    Done a        -> ([],a)
    WriteLine s k -> let (ss,a) = runTeletypePurely xs k in (s:ss,a) 
    ReadLine f    -> case xs of
        []        -> runTeletypePurely [] (f "") -- missing input <-> "" input 
        (s:ss)    -> runTeletypePurely ss (f s) 

