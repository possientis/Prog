type Foo = Integer

x :: Foo
x = 2

y :: Foo
y = 3

z :: Bool
z = (x == y)  -- Foo automatically an instance of Eq, but ...


class Bar a where
  foo :: a -> a

-- cannot make Foo (a synonym) instance of a class
{-
instance Bar Foo where
  foo x = x
-}
