{-# LANGUAGE DuplicateRecordFields #-}

data Person     = Person    { id :: Int }
data Animal     = Animal    { id :: Int }
data Vegetable  = Vegetable { id :: Int }


test :: Int
test = id (Person 1)  -- projection still not supported 


