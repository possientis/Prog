-- Bridge design patter

-- bridge implementation interface
class IDrawAPI a where
  drawCircle :: a -> Int -> Int -> Int -> IO ()

-- concrete bridge implementation classes implementing DrawAPI interface
data RedCircle = RedCircle
instance IDrawAPI RedCircle where
  drawCircle _ radius x y =   putStr "Drawing Circle[ color: red  , radius: "
                          >>  putStr (show radius)
                          >>  putStr ", x: " >> putStr (show x)
                          >>  putStr ", y: " >> putStr (show y)
                          >>  putStrLn "]"

data GreenCircle = GreenCircle
instance IDrawAPI GreenCircle where
  drawCircle _ radius x y =   putStr "Drawing Circle[ color: green, radius: "
                          >>  putStr (show radius)
                          >>  putStr ", x: " >> putStr (show x)
                          >>  putStr ", y: " >> putStr (show y)
                          >>  putStrLn "]"

data DrawAPI = DrawAPIr RedCircle | DrawAPIg GreenCircle
instance IDrawAPI DrawAPI where
  drawCircle (DrawAPIr a) radius x y = drawCircle a radius x y
  drawCircle (DrawAPIg a) radius x y = drawCircle a radius x y

makeRedAPI = (DrawAPIr RedCircle)
makeGreenAPI = (DrawAPIg GreenCircle)

-- create an abstract class Shape using the DrawAPI interface.
class IShape a where  -- just the interface, no data
  draw :: a -> IO ()

data Shape = Shape {_drawAPI::DrawAPI}
instance IShape Shape where
  draw _ = putStrLn "Shape::draw is not implemented"

-- create concrete class implementing the Shape interface (abstract class)
data Circle = Circle {_x::Int, _y::Int, _radius::Int, _shape::Shape}
makeCircle :: Int -> Int -> Int -> DrawAPI -> Circle
makeCircle x y radius drawAPI = Circle x y radius (Shape drawAPI)
instance IShape Circle where
  draw (Circle x y radius (Shape drawAPI)) = drawCircle drawAPI radius x y

-- Use Shape and DrawAPI classes to draw different colored circles
main = do 
   -- implementation of concrete circles selected at run time.
  let redCircle = makeCircle 100 100 10 makeRedAPI;
      greenCircle = makeCircle 100 100 10 makeGreenAPI in do 
      draw redCircle
      draw greenCircle

