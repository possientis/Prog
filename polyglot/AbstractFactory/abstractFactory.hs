import Data.Char

class IShape a where
  draw :: a -> IO()

data COLOR = RED | GREEN | BLUE
instance Show COLOR where
  show RED = "red"
  show GREEN = "green"
  show BLUE = "blue"

asString :: COLOR -> String
asString = show

class IShape a => IAbstractShape a where
 color :: a -> COLOR 

data Rectangle = Rectangle COLOR

instance IShape Rectangle where
  draw x = putStrLn ("Drawing " ++ asString (color x) ++ " rectangle")

instance IAbstractShape Rectangle where
  color (Rectangle x) = x

data Square = Square COLOR

instance IShape Square where
  draw x = putStrLn ("Drawing " ++ asString (color x) ++ " square")

instance IAbstractShape Square where
  color (Square x) = x

data Circle = Circle COLOR

instance IShape Circle where
  draw x = putStrLn ("Drawing " ++ asString (color x) ++ " circle")

instance IAbstractShape Circle where
  color (Circle x) = x

-- combining typeclass instances into one type to be used as factory return type
data Shape = MkRectangle Rectangle | MkSquare Square | MkCircle Circle
instance IShape Shape where
  draw (MkRectangle x) = draw x
  draw (MkSquare x) = draw x
  draw (MkCircle x) = draw x

class IAbstractShapeFactory a where
  getColor :: a -> COLOR
  getShape :: a -> String -> Maybe Shape
  getShape x shapeType = case map toUpper shapeType of
    "CIRCLE"    -> Just (MkCircle (Circle (getColor x)))
    "RECTANGLE" -> Just (MkRectangle (Rectangle (getColor x)))
    "SQUARE"    -> Just (MkSquare (Square (getColor x)))
    otherwise   -> Nothing     
  
data RedShapeFactory = RedShapeFactory
instance IAbstractShapeFactory RedShapeFactory where
  getColor x = RED

data GreenShapeFactory = GreenShapeFactory
instance IAbstractShapeFactory GreenShapeFactory where
  getColor x = GREEN

data BlueShapeFactory = BlueShapeFactory
instance IAbstractShapeFactory BlueShapeFactory where
  getColor x = BLUE

data AbstractShapeFactory = MkRED RedShapeFactory
                          | MkGREEN GreenShapeFactory
                          | MkBLUE BlueShapeFactory

instance IAbstractShapeFactory AbstractShapeFactory where
  getColor (MkRED x) = getColor x
  getColor (MkGREEN x) = getColor x
  getColor (MkBLUE x) = getColor x

class IFactoryProducer a where
  getFactory :: a -> String -> Maybe AbstractShapeFactory
  getFactory x factoryType = case map toUpper factoryType of
    "RED"       -> Just (MkRED RedShapeFactory)
    "GREEN"     -> Just (MkGREEN GreenShapeFactory)
    "BLUE"      -> Just (MkBLUE BlueShapeFactory)
    otherwise   -> Nothing

data FactoryProducer = FactoryProducer
instance IFactoryProducer FactoryProducer

main = do
  let producer = FactoryProducer
      Just redFactory = getFactory producer "Red" 
      Just greenFactory = getFactory producer "Green"
      Just blueFactory = getFactory producer "Blue"
      Just shape1 = getShape redFactory "CIRCLE"
      Just shape2 = getShape redFactory "RECTANGLE"
      Just shape3 = getShape redFactory "SQUARE"
      Just shape4 = getShape greenFactory "CIRCLE"
      Just shape5 = getShape greenFactory "RECTANGLE"
      Just shape6 = getShape greenFactory "SQUARE"
      Just shape7 = getShape blueFactory "CIRCLE"
      Just shape8 = getShape blueFactory "RECTANGLE"
      Just shape9 = getShape blueFactory "SQUARE"
    in 
       draw shape1 >> draw shape2 >> draw shape3 >>
       draw shape4 >> draw shape5 >> draw shape6 >>
       draw shape7 >> draw shape8 >> draw shape9



