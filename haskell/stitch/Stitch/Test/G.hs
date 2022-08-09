{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE RankNTypes     #-}

module Stitch.Test.G 
  ( main
  ) where

import Data.Kind

data G :: Type -> Type where
  ConBool :: G Bool
  ConInt  :: G Int
  

match :: forall a . G a -> a
match ConBool = True
match ConInt  = 42

main :: IO ()
main = do
  print . match $ ConBool
  print . match $ ConInt
