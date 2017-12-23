{-# LANGUAGE FlexibleContexts #-}

class MyClass a

-- ok
instance (MyClass a) =>  MyClass [a]

-- need FlexibleContexts because of 'Maybe'
instance (MyClass (Maybe a)) => MyClass (Either a b)
