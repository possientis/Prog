import Control.Monad
import System.Directory
import Data.List
import System.IO
import Test.QuickCheck
import Data.Hashable
import System.Process



when' :: (Monad m) => Bool -> m () -> m ()
when'  False _ = return ()
when' True  x = x


main = do
  when' True  (putStrLn "hello")
  when' False (putStrLn "this should never appear") 

