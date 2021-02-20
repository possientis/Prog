module  Console
    (   Console (..)
    ,   runConsole
    )   where

data Console = Console
    { text   :: String
    , action :: String -> IO ()
    }

runConsole :: Console -> IO ()
runConsole c = do
    putStrLn . text $ c
    input <- getLine
    action c input


