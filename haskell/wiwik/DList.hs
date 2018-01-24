import Data.DList 
import Control.Monad.Writer


logger :: Writer (DList Int) ()
logger = replicateM_ 100000 $ tell (singleton 0)

logger' :: Writer [Int] ()
logger' = replicateM_ 100000 $ tell [0]

main :: IO ()
main = do
    print $ logger

