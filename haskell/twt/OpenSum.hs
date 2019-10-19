{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE PolyKinds              #-}

import Data.Kind
import Fcf

data OpenSum (f :: k -> Type) (ts :: [k]) :: Type where
    UnsafeOpenSum :: Int -> f t -> OpenSum f ts 

--Giving up
--type FindElem (key :: k) (ts :: [k]) = FromMaybe Stuck =<< FindIndex (TyEq key) ts
