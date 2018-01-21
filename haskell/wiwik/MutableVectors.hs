import GHC.Prim

import Control.Monad
import Control.Monad.ST
import Control.Monad.Primitive
import Data.Vector.Unboxed (Vector, freeze)
import Data.Vector.Unboxed.Mutable


example :: PrimMonad m => m (Vector Int)
example = do
    v <- new 10
    forM_ [0..9] $ \i ->
        write v i (2*i)
    freeze v


-- vector computation in IO
vecIO :: IO (Vector Int)
vecIO = example


-- vector computation in ST
vecST :: ST s (Vector Int)
vecST = example


main :: IO ()
main = do
    vecIO >>= print
    print $ runST vecST


