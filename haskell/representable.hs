{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeFamilies #-}

data F a = MkF { unF :: a} deriving (Functor, Eq)

data A = A
data B = B deriving Eq

alpha :: forall x . (String -> x ) -> F x 
alpha = undefined


alpha' :: (String -> x ) -> F x 
alpha' = undefined

f :: A -> B
f A = B

f1 = fmap f . alpha
f2 = alpha . fmap f

h :: String -> A
h _ = A

g1 = fmap f (alpha h)
g2 = alpha (f . h)

beta :: forall x . F x -> (String -> x)
beta = undefined


-- The list functor is not representable

gamma :: forall x. (Int -> x) -> [x]
gamma h = map h [12]

gamma_inverse :: forall x. [x] -> (Int -> x)
gamma_inverse  = undefined -- cant do it 


class Representable f where
    type Rep f :: *   -- the 'a' in the natural isomorphism C(a,-) => f
    tabulate   :: forall x. (Rep f -> x) -> f x
    index      :: forall x. f x -> Rep f -> x 


data Stream a = Cons a (Stream a)

instance Representable Stream where
    type Rep Stream = Integer
    tabulate f = Cons (f 0) (tabulate (f . (+1)))
    index (Cons b bs) n = if n == 0 then b else index bs (n - 1)





