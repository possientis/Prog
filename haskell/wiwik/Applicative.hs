import Network.HTTP
import Control.Applicative


example1 :: Maybe Integer
example1 = (+) <$> m1 <*> m2 where
    m1 = Just 3
    m2 = Nothing


example2 :: [(Int,Int,Int)] 
example2 = (,,) <$> m1 <*> m2 <*> m3 where
    m1 = [1,2]
    m2 = [10,20]
    m3 = [100,200]

example3 :: IO String
example3 = (++) <$> fetch1 <*> fetch2 where
    fetch1 = simpleHTTP (getRequest "http://www.yahoo.com") >>= getResponseBody
    fetch2 = simpleHTTP (getRequest "http://www.haskell.org/") >>= getResponseBody
    

