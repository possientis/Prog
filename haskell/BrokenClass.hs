{-# LANGUAGE FlexibleInstances #-} -- so we can make [(String,a)] an instance

import JSONclass

instance (JSON a) => JSON [a] where
  toJValue = undefined
  fromJValue = undefined 


instance (JSON a) => JSON [(String,a)] where
  toJValue = undefined
  fromJValue = undefined
