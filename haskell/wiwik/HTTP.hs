
import Network.HTTP.Client
import Network.HTTP.Types

import Control.Concurrent.Async

type URL = String

get :: Manager -> URL -> IO Int
get m url = do
    req <- parseUrlThrow url
    statusCode <$> responseStatus <$> httpNoBody req m


single :: IO Int
single = do
    m <- newManager defaultManagerSettings
    get m "http://neverssl.com"

parallel :: IO [Int]
parallel = do
    m <- newManager defaultManagerSettings
    let urls = replicate 10 "http://neverssl.com"
    mapConcurrently (get m) urls


main :: IO ()
main = do
    single   >>= print
    parallel >>= print
