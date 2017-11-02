{-# LANGUAGE StrictData #-}

-- StrictData makes all constructor fields strict by default
-- on any module it is enabled on
import Data.Text

data Employee = Employee
    {   name :: Text
    ,   age  :: Int
    } 

-- is equivalent to

data Employee' = Employee'
    {   name' :: !Text
    ,   age'  :: !Int
    }
