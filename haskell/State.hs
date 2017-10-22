--import Control.Monad.State
import MonadState

test :: State Int Int
test = do
    put 3
    modify (+1)
    get

main :: IO ()
main = print $ execState test 0
