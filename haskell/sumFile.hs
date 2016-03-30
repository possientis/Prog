import System.IO
import qualified Data.ByteString as ByteString            -- strict binary or text data
import qualified Data.ByteString.Lazy as ByteString.Lazy  -- lazy binary or text data (also named 'ByteString')

-- strict best when need random access, and not so concerned with memory footprint

-- String is not efficient data type, consider using ByteString and ByteString.Lazy
main = do
  inh <- openFile "input.txt" ReadMode
  contents <- hGetContents inh
  print (sumFile contents) where
    sumFile = sum . map read . words
  
  
