import Data.Csv

import qualified Data.Vector as V
import qualified Data.ByteString.Lazy as BL

type ErrorMsg = String
type CsvData = V.Vector (V.Vector BL.ByteString)


example :: FilePath -> IO (Either ErrorMsg CsvData)
example fname = do
    contents <- BL.readFile fname
    return $ decode NoHeader contents


main :: IO ()
main = do 
    res <- example "example.csv"
    print res
