-- Factory design pattern
import Data.Char  -- toUpper

class IShape a where
  draw :: a -> IO ()

data Rectangle = Rectangle
instance IShape Rectangle where
  draw Rectangle = putStrLn "Inside Rectangle::draw() method."

data Square = Square
instance IShape Square where
  draw Square = putStrLn "Inside Square::draw() method."

data Circle = Circle
instance IShape Circle where
  draw Circle = putStrLn "Inside Circle::draw() method."

data Shape = MkShapeR Rectangle | MkShapeS Square | MkShapeC Circle
instance IShape Shape where
  draw (MkShapeR x) = draw x
  draw (MkShapeS x) = draw x
  draw (MkShapeC x) = draw x

data ShapeFactory = ShapeFactory
getShape :: ShapeFactory -> String -> Maybe Shape
getShape ShapeFactory shapeType = case (map toUpper shapeType) of
   "CIRCLE"    -> Just (MkShapeC Circle)
   "RECTANGLE" -> Just (MkShapeR Rectangle)
   "SQUARE"    -> Just (MkShapeS Square)
   otherwise   -> Nothing

main = do 
  let shapeFactory = ShapeFactory
      Just shape1 = getShape shapeFactory "CIRCLE"
      Just shape2 = getShape shapeFactory "RECTANGLE"
      Just shape3 = getShape shapeFactory "SQUARE"
    in do
      draw shape1
      draw shape2
      draw shape3





