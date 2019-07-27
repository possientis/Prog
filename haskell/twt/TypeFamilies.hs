{-# LANGUAGE TypeFamilies   #-}
{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE PolyKinds      #-}
{-# LANGUAGE TypeOperators  #-}

-- Or :: Bool -> Bool -> Bool
type family Or (x :: Bool) (y :: Bool) :: Bool where 
    Or 'True  y = 'True
    Or 'False y = y


type Or11 = Or 'True  'True     -- :: Bool, !kind T11 = 'True
type Or10 = Or 'True  'False    -- 'True
type Or01 = Or 'False 'True     -- 'True
type Or00 = Or 'False 'False    -- 'False

-- And :: Bool -> Bool -> Bool
type family And (x :: Bool) (y :: Bool) :: Bool where
    And 'False y = 'False
    And 'True  y = y 

type And11 = And 'True  'True   -- 'True
type And10 = And 'True  'False  -- 'False
type And01 = And 'False 'True   -- 'False
type And00 = And 'False 'False  -- 'False


-- Not :: Bool -> Bool
type family Not (x :: Bool) :: Bool where
    Not 'True  = 'False
    Not 'False = 'True


type N1 = Not 'True             -- 'False
type N0 = Not 'False            -- 'True

-- not useful, as type families need to be saturated
type family Map (f :: a -> b) (xs :: [a]) :: [b] where
    Map f '[]       = '[]
    Map f (x ': xs) = f x ': Map f xs

-- fails, attempting to use Not without an argument
-- type T1 = Map Not '[ 'True, 'False, 'True ]

-- Foo :: Bool -> Bool -> Bool
type family Foo (x :: Bool) (y :: Bool) :: Bool --

-- Bar :: * -> * -> Bool -> Bool -> Bool
type family Bar x y :: Bool -> Bool -> Bool

