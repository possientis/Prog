{-# LANGUAGE FlexibleInstances, TypeSynonymInstances  #-}

type IntList = [Int]

class MyClass a

-- FlexibleInstances required
--instance MyClass [Int]

-- don't get it
instance MyClass IntList

