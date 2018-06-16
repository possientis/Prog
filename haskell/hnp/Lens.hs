{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts #-}

import Control.Lens
import Control.Monad.State.Class

data Point = Point 
    { _x :: Float
    , _y :: Float
    } deriving Show

data Entity = Entity
    { _position  :: Point
    , _direction :: Float
    } deriving Show

data World = World
    { _entities :: [Entity]
    }

makeLenses ''Point
makeLenses ''Entity
makeLenses ''World


updateWorld :: MonadState World m => m ()
updateWorld = do
    -- move the first entity
    entities . ix 0 . position . x += 1

    -- do some operation on all of them
    entities . traversed . position %= \p -> p -- `pointAdd` ...

    -- or only on a subset
    entities . traversed . filtered (\e -> e ^. position.x > 100) %= \p -> p -- ...



main :: IO ()
main = do
    print p
    print $ p ^. x
    print $ p ^. y
    print $ set x 10 p
    print $ p & x +~3
    print $ ("a", 1) ^. _1          -- "a"
    print $ ("a", 1) & _1 .~ "b"    -- ("b",1)
    print $ ("a", 1) & _2 %~ (+3)   -- ("a",4)
    print $ (1, 2) & both *~ 2      -- (2,4)


p :: Point
p = Point 5 6
