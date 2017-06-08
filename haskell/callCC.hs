-- callCC is call-with-current-continuation
import Cont -- homemade continuation monad

-- without callCC
sq :: Int -> Cont r Int
sq  n = return (n ^ 2)

--with callCC
sqCCC :: Int -> Cont r Int
sqCCC n = callCC $ \k -> k (n ^ 2)

-- Naive reasoning to try and make sense of callCC:
--
-- An element of type Cont r a is essentially a map :: (a -> r) -> r
-- It can be viewed as an interrupted computation returning an 'a', 
-- which when applied a computation 'a -> r' returns an 'r'.
--
-- In short, we can regard an element of type Cont r a as an interrupted
-- computation which returns an 'a'.
--
-- What is a continuation? it is a computation which takes an 'a'
-- and returns an interrupted computation returning a 'b'.
-- In short, a continuation is an element of type a -> Cont r b
--
-- The function callCC which stands for the scheme call-with-current-continuation
-- takes a single function f :: t -> s as argument (We shall discuss the types t
-- and s below). callCC simply calls the function f with an argument equal to
-- the 'current continuation'. What is the current continuation?   
-- Well callCC returns some interrupted computation returning an 'a'.
-- So callCC is returning an element of Cont r a. The current continuation
-- therefore takes an 'a' and return some Cont r b. The actual semantics
-- of the current continuation depends on the code 'after callCC'.
--
-- What can we say about the type of callCC at this stage? It returns 
-- an interrupted computation of type Cont r a having taken a function 
-- f :: t -> s as argument. Hence callCC :: (t -> s) -> Cont r a.
-- Furthermore, the function being passed as argument itself takes 
-- a single argument (the current continuation) of type a -> Cont r b.
-- Hence callCC :: ((a -> Cont r b) -> s) -> Cont r a. Furthemore,
-- callCC f which simply calls f :: t-> s on the current continuation,
-- returns the same value as f (which we have assumed to be some Cont r a)
-- Hence we must have s = Cont r a and consequently:
-- callCC :: ((a -> Cont r b) -> Cont r a) -> Cont r a
-- callCC f where f :: (a -> Cont r b) -> Cont r a
-- callCC f = cont (\k -> ... some 'r') where k :: a -> r


callCC :: ((a -> Cont r b) -> Cont r a) -> Cont r a
callCC f = undefined      


