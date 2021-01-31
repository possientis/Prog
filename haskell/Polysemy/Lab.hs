module  Lab
    (   main
    )   where

import Teletype

main :: IO ()
main = runTeletype prog
--main = print . fst . runTeletypePurely ["john"] $ prog

prog :: Teletype ()
prog = do
    writeLine "What is your name:"
    s <- readLine 
    writeLine $ "Hello " ++ s ++ " please to meet you."



