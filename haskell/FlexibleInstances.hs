{-# LANGUAGE FlexibleInstances #-}

class MyClass a


instance MyClass (Maybe a)

-- 'Either e a' would be fine but 'Either String a' require FlexibleInstances
instance MyClass (Either String a)
