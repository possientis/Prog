module  Lab
    (   main
    )   where

import Control.Monad
import Teletype

main :: IO ()
main = runTeletype prog
--main = print . fst . runTeletypePurely ["john"] $ prog

prog :: Teletype ()
prog = forever $ do
    writeLine "What is your name:"
    s <- readLine 
    writeLine $ "Hello " ++ s ++ " please to meet you."



