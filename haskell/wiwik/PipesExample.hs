import Pipes
import Pipes.Prelude as P
import Control.Monad
import Control.Monad.Identity

a :: Producer Int Identity ()
a = forM_ [1..10] yield


b :: Pipe Int Int Identity ()
b = forever $ do
    x <- await
    yield (x*2)
    yield (x*3)
    yield (x*4)

c :: Pipe Int Int Identity ()
c = forever $ do
    x <- await
    if (x `mod` 2) == 0
        then yield x
        else return ()

result :: [Int]
result = P.toList $ a >-> b >-> c
-- [2,4,4,6,8,6,12,8,12,16,10,20,12,18,24,14,28,16,24,32,18,36,20,30,40]

