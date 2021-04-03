{-# LANGUAGE LambdaCase     #-}
{-# LANGUAGE TypeOperators  #-}

module  Teletype
    (   Teletype   (..)
    ,   readLine
    ,   writeLine
    ,   runTeletype
    ,   runTeletypePurely
    )   where 

import Free

readLine :: Free Teletype String
readLine = Impure $ ReadLine Pure

writeLine :: String -> Free Teletype ()
writeLine s = Impure $ WriteLine s $ Pure ()

runTeletype :: Free Teletype a -> IO a
runTeletype = runFree interpIO

runTeletypePurely :: [String] -> Free Teletype a -> ([String], a)
runTeletypePurely xs = \case
    Pure a                  -> ([],a)
    Impure (WriteLine s k) -> let (ss,a) = runTeletypePurely xs k in (s:ss,a) 
    Impure (ReadLine f)    -> case xs of
        []        -> runTeletypePurely [] (f "") -- missing input <-> "" input 
        (s:ss)    -> runTeletypePurely ss (f s) 

data Teletype r 
    = WriteLine String r
    | ReadLine (String -> r)

instance Functor Teletype where
    fmap f (WriteLine s a) = WriteLine s (f a)
    fmap f (ReadLine g)    = ReadLine (f . g)

interpIO :: Teletype :-> IO
interpIO (WriteLine msg a) = putStrLn msg >> pure a 
interpIO (ReadLine f) = getLine >>= (pure . f)

