{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}

import GHC.Exts (Constraint)

-- Show :: * -> Constraint

data Some :: (* -> Constraint) -> * where
  Some :: c a => a -> Some c


showSomething :: Some Show -> String
showSomething (Some thing) = show thing


heteroList :: [Some Show]
heteroList = [Some True, Some (5::Int), Some (Just ())]

instance Show (Some Show) where
  show (Some thing) = show thing
