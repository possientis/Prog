module  Console
    (   Console (..)
    )   where

data Console = Console
    { _text   :: String
    , _action :: String -> IO ()
    }


