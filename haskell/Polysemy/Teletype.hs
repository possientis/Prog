{-# LANGUAGE LambdaCase     #-}

module  Teletype
    (   Teletype    (..)
    ,   TeletypeF   (..)
    ,   readLine
    ,   readLine'
    ,   writeLine
    ,   writeLine'
    ,   runTeletype
    ,   runTeletype'
    ,   runTeletypePurely
    ,   runTeletypePurely'
    ,   toFree
    ,   fromFree
    )   where 

import Control.Monad

import Free

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

readLine' :: Free TeletypeF String
readLine' = Impure (ReadLineF Pure) 

writeLine :: String -> Teletype ()
writeLine s = WriteLine s $ Done ()

writeLine' :: String -> Free TeletypeF ()
writeLine' s = Impure (WriteLineF s $ Pure ()) 

runTeletype :: Teletype a -> IO a
runTeletype = \case
    Done a        -> return a
    WriteLine s k -> putStrLn s >>  runTeletype k
    ReadLine f    -> getLine    >>= runTeletype . f

runTeletype' :: Free TeletypeF a -> IO a
runTeletype' = \case
    Pure a                  -> return a
    Impure (WriteLineF s k) -> putStrLn s >>  runTeletype' k
    Impure (ReadLineF f)    -> getLine    >>= runTeletype' . f 

runTeletypePurely :: [String] -> Teletype a -> ([String], a)
runTeletypePurely xs = \case
    Done a        -> ([],a)
    WriteLine s k -> let (ss,a) = runTeletypePurely xs k in (s:ss,a) 
    ReadLine f    -> case xs of
        []        -> runTeletypePurely [] (f "") -- missing input <-> "" input 
        (s:ss)    -> runTeletypePurely ss (f s) 

runTeletypePurely' :: [String] -> Free TeletypeF a -> ([String], a)
runTeletypePurely' xs = \case
    Pure a                  -> ([],a)
    Impure (WriteLineF s k) -> let (ss,a) = runTeletypePurely' xs k in (s:ss,a) 
    Impure (ReadLineF f)    -> case xs of
        []        -> runTeletypePurely' [] (f "") -- missing input <-> "" input 
        (s:ss)    -> runTeletypePurely' ss (f s) 

data TeletypeF r 
    = WriteLineF String r
    | ReadLineF (String -> r)

instance Functor TeletypeF where
    fmap f (WriteLineF s a) = WriteLineF s (f a)
    fmap f (ReadLineF g)    = ReadLineF (f . g)

toFree :: Teletype a -> Free TeletypeF a
toFree (Done a)        = Pure a
toFree (WriteLine s k) = Impure (WriteLineF s (toFree k))
toFree (ReadLine g)    = Impure (ReadLineF (toFree . g))

fromFree :: Free TeletypeF a -> Teletype a
fromFree (Pure a)                  = Done a
fromFree (Impure (WriteLineF s k)) = WriteLine s (fromFree k)
fromFree (Impure (ReadLineF g))    = ReadLine (fromFree . g)

