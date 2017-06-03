-- callCC is call-with-current-continuation
import Cont -- homemade continuation monad

-- without callCC
sq :: Int -> Cont r Int
sq  n = return (n ^ 2)

--with callCC
sqCCC :: Int -> Cont r Int
sqCCC n = callCC $ \k -> k (n ^ 2)


callCC :: ((a -> Cont r b) -> Cont r a) -> Cont r a
callCC = undefined


