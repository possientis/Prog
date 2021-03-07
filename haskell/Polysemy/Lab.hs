module  Lab
    (   main
    ,   prog
    ,   prog'
    )   where

import Control.Monad

import Free
import Teletype

main :: IO ()
main = runTeletype' prog'
--main = print . fst . runTeletypePurely ["john"] $ prog

prog :: Teletype ()
prog = forever $ do
    writeLine "[Norm] What is your name:"
    s <- readLine 
    writeLine $ "Hello " ++ s ++ " please to meet you."

prog' :: Free TeletypeF ()
prog' = forever $ do
    writeLine' "[Free] What is your name:"
    s <- readLine' 
    writeLine' $ "Hello " ++ s ++ " please to meet you."

_res :: [String]
_res = take 2 . fst . runTeletypePurely ["john"] $ prog


_res' :: [String]
_res' = take 2 . fst . runTeletypePurely' ["john"] $ prog'

