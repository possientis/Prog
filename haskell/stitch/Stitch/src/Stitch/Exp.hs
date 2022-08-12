module  Stitch.Exp
  ( Ctx
  ) where

import Data.Kind

import Stitch.Data.Vec

-- | A context is just a vector of types
type Ctx n = Vec n Type

