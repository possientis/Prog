import Data.Dynamic
-- import Data.Maybe

dynamicBox :: Dynamic
dynamicBox = toDyn (3.14 :: Double)

ex1 :: Maybe Int
ex1 = fromDynamic dynamicBox    -- Nothing

ex2 :: Maybe Double
ex2 = fromDynamic dynamicBox    -- Just 3.14

ex3 :: Int
ex3 = fromDyn dynamicBox 0      -- 0


ex4 :: Double
ex4 = fromDyn dynamicBox 0.0    -- 3.14
