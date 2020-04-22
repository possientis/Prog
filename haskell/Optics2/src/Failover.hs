module  Failover
    (   failover
    ,   ex1
    )   where

import Data.Char
import Data.Monoid
import Control.Applicative

import Control.Lens hiding (failover)
import qualified Control.Lens as L (failover)
--
-- Actual signature
failover :: Alternative m => LensLike ((,) Any) s t a b -> (a -> b) -> s -> m t
failover = undefined

-- specialized
-- failover :: Traversal s t a b -> (a -> b) -> s -> Maybe t


ex1 :: Maybe String
ex1 = "abcd" & L.failover (ix 6) toUpper
