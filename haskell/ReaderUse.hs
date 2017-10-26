--import Control.Monad.Reader
import Reader

data MyContext = MyContext
    { foo :: String
    , bar :: Int
    } deriving (Show)

computation :: Reader MyContext (Maybe String)
computation = do
    n <- asks bar
    x <- asks foo
    if n > 0
        then return (Just x)
        else return Nothing

example1 :: Maybe String
example1 = runReader computation $ MyContext "hello" 1

example2 :: Maybe String
example2 = runReader computation $ MyContext "haskell" 0



    
