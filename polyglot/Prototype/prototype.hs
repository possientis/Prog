-- Prototype design pattern
-- Imagine that in order to instantiate certain objects we need to carry out
-- expensive database queries. In order to improve performance, it would 
-- be beneficial to cache whatever object is created from the database
-- and return a copy of the cached object whenever a subsequent request
-- for object instantiation arises.

import Data.Map -- Map k v

class IShape a where
  draw  :: a -> IO()
  clone :: a -> a
  clone x = x               -- immutable objects come in handy
  setId :: a -> String -> a -- returns new immutable object 
  getId :: a -> String


data Rectangle = MkRectangle String
instance IShape Rectangle where
  draw (MkRectangle x) = putStrLn "Inside Rectangle::draw() method."
  setId _ = MkRectangle 
  getId (MkRectangle x) = x

data Square = MkSquare String
instance IShape Square where
  draw (MkSquare x) = putStrLn "Inside Square::draw() method."
  setId _ = MkSquare
  getId (MkSquare x) = x

data Circle = MkCircle String
instance IShape Circle where
  draw (MkCircle x) = putStrLn "Inside Circle::draw() method."
  setId _ = MkCircle
  getId (MkCircle x) = x
  

data Shape = MkRShape Rectangle | MkSShape Square | MkCShape Circle
instance IShape Shape where
  draw (MkRShape x) = draw x
  draw (MkSShape x) = draw x
  draw (MkCShape x) = draw x
  setId (MkRShape x) s = MkRShape (setId x s)
  setId (MkSShape x) s = MkSShape (setId x s)
  setId (MkCShape x) s = MkCShape (setId x s)
  getId (MkRShape x) = getId x
  getId (MkSShape x) = getId x
  getId (MkCShape x) = getId x

newRectangle  = MkRShape (MkRectangle "")
newSquare     = MkSShape (MkSquare "")
newCircle     = MkCShape (MkCircle "")

class IPrototypeManager a where
  getShape  :: a -> String -> Shape
  loadCache :: a -> a

data PrototypeManager = MkManager (Map String Shape)
instance IPrototypeManager PrototypeManager where
  loadCache _ = let
    rectangle = setId newRectangle "1"
    square = setId newSquare "2"
    circle = setId newCircle "3"
    map1 = insert "1" rectangle empty
    map2 = insert "2" square map1
    map3 = insert "3" circle map2
    in MkManager map3
  getShape (MkManager map) key = map ! key

newPrototypeManager = MkManager empty

main = let
    -- need a prototype manager with a few registered prototypes
    manager = loadCache newPrototypeManager
    -- prototype manager can now be used as factory object
    clonedShape1 = getShape manager "1"
    clonedShape2 = getShape manager "2"
    clonedShape3 = getShape manager "3"
    in do
    draw clonedShape1
    draw clonedShape2
    draw clonedShape3
  
