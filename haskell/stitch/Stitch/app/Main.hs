{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TypeApplications #-}

module Main
  ( main
  ) where

import Type.Reflection

import Stitch.Data.Exists
import Stitch.Data.Fin
import Stitch.Data.Nat
import Stitch.Data.Vec
import Stitch.Data.Singletons

import Stitch.Type


main :: IO ()
main = do 
  print Zero
  print $ Succ Zero
  print FZ
  print $ FS FZ
  print (VNil :: Vec Int 'Zero)
  print (sing :: Sing 'Zero)
  print test1
  print $ mkTy @Int
  print $ typeRep @Int
  print $ typeOf (3 :: Int)
