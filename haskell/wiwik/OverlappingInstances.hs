{-# LANGUAGE    MultiParamTypeClasses, 
                FlexibleInstances,
                OverlappingInstances -- deprecated
#-}

-- MultiParamTypeClasses needed here
class MyClass a b where
    fn :: (a,b)

-- FlexibleInstances needed here
instance MyClass Int b where
    fn = error "b"

-- fine , but will need OverlappingInstances if 'fn' called
instance MyClass a Int where
    fn = error "a"

instance MyClass Int Int where
    fn = error "c"

example :: (Int,Int)
example = fn 

