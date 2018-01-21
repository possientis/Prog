import Prelude hiding (lookup)

import Control.Monad.ST
import Data.HashTable.ST.Basic

type HT s = HashTable s String String


set :: ST s (HT s)
set = do
    ht <- new
    insert ht "key" "value1"
    return ht

get :: HT s -> ST s (Maybe String)
get ht = do
    val <- lookup ht "key"
    return val


ex :: Maybe String
ex = runST (set >>= get)


main :: IO ()
main = do
    print ex
