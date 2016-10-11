-- Builder Design Pattern
-- The main idea behind the builder design pattern is
-- to provide an abstract interface for a 'builder object'
-- A concrete builder object is not a factory object which returns
-- a ready-made object of a certain type. A concrete builder object
-- should be viewed as a toolbox allowing someone else (that someone
-- else is called 'a director' within the context of the builer design
-- pattern) to build an object of some type according to some plan.

-- Let us define a possible 'director' class, whose purpose
-- it is to manufacture meals

-- A director is constructed from a builder, which specifies its toolbox
data DirectorCook a = MakeCook a
getBuilder :: MealBuilder a => DirectorCook a -> a
getBuilder (MakeCook x) = x

-- This is the main method of the director, which creates an object
-- based on some logic and algorithm which is encapsulated in the
-- method body, and uses the tools provided by the builder interface.
-- the makeMeal method returns a new immutable DirectorCook, after
-- meal has been made.
makeMeal :: MealBuilder a => DirectorCook a -> DirectorCook a
makeMeal (MakeCook x) = MakeCook(addDrink (addBurger (startNewMeal x)))

-- Note that the manufacture algorithm contained in the director
-- is very general and does not tell us anything about the type of
-- the object being created, let alone its internal representation.
class MealBuilder a where
  startNewMeal :: a -> a  -- returns new immutable object, after meal started
  addBurger    :: a -> a  -- returns new immutable object, after burger added
  addDrink     :: a -> a  -- returns new immutable object, after drink added
  getMeal      :: a -> Meal

-- We can implement MealBuilder in many different ways, so as to 
-- construct objects of many possible types which do not even need
-- to be related by a common base class 'Meal' or anything beyond 'Object'

-- However, at some point we need to retrieve the constructed object
-- so there must be some method 'getObject'. In general, because the
-- return type of 'getObject' may be arbitrary, the method declaration
-- cannot be part of the interface MealBuilder as this would constrain
-- the implementation to a specific type being constructed.

-- In this example, we shall consider two concrete implementations of
-- MealBuilder, a 'VegetarianMealBuilder' and a 'NonVegetarianMealBuilder'.
-- Both implementation will allow the construction of objects of the same
-- type, but one should remember that this need not be the case when 
-- applying the builder design pattern.

-- Concrete implementations of MealBuilder will hold an object of type
-- Meal (the object being constructed), and will have a getObject() method.

data VegetarianMealBuilder = VegetarianMealBuilder Meal
instance MealBuilder VegetarianMealBuilder where

  startNewMeal _ = VegetarianMealBuilder (Meal [])

  addBurger (VegetarianMealBuilder meal) 
    = VegetarianMealBuilder (addItem meal (MkVegBurger VegBurger))

  addDrink (VegetarianMealBuilder meal)  
    = VegetarianMealBuilder (addItem meal (MkCoke Coke))

  getMeal (VegetarianMealBuilder meal) = meal

data NonVegetarianMealBuilder = NonVegetarianMealBuilder Meal
instance MealBuilder NonVegetarianMealBuilder where

  startNewMeal _ = NonVegetarianMealBuilder (Meal [])

  addBurger (NonVegetarianMealBuilder meal) 
    = NonVegetarianMealBuilder (addItem meal (MkChickenBurger ChickenBurger))

  addDrink (NonVegetarianMealBuilder meal) 
    = NonVegetarianMealBuilder (addItem meal (MkPepsi Pepsi))

  getMeal (NonVegetarianMealBuilder meal) = meal

data Meal = Meal [Item]

addItem :: Meal -> Item -> Meal -- return new immutable Meal, after item added
addItem (Meal xs) x = Meal (x:xs)

getCost :: Meal -> Double
getCost (Meal []) = 0.0
getCost (Meal (x:xs)) = (price x) + getCost (Meal xs) 

showItems :: Meal -> IO ()
showItems (Meal []) = return ()
showItems (Meal (x:xs)) =
  putStr "Item : "      >> putStr (name x)            >>
  putStr ", Packing : " >> putStr (pack (packing x))  >>
  putStr ", Price : "   >> putStrLn (show (price x))  >>
  showItems (Meal xs)

class IItem a where
  price   :: a -> Double
  name    :: a -> String
  packing :: a -> Packing

data Item = MkVegBurger VegBurger
          | MkChickenBurger ChickenBurger
          | MkCoke Coke
          | MkPepsi Pepsi

instance IItem Item where
  price (MkVegBurger VegBurger) = price VegBurger
  price (MkChickenBurger ChickenBurger) = price ChickenBurger
  price (MkCoke Coke) = price Coke
  price (MkPepsi Pepsi) = price Pepsi
  name (MkVegBurger VegBurger) = name VegBurger
  name (MkChickenBurger ChickenBurger) = name ChickenBurger
  name (MkCoke Coke) = name Coke
  name (MkPepsi Pepsi) = name Pepsi
  packing (MkVegBurger VegBurger) = packing VegBurger
  packing (MkChickenBurger ChickenBurger) = packing ChickenBurger
  packing (MkCoke Coke) = packing Coke
  packing (MkPepsi Pepsi) = packing Pepsi


class IPacking a where
  pack :: a -> String

data Wrapper = Wrapper
instance IPacking Wrapper where
  pack Wrapper = "Wrapper"

data Bottle = Bottle
instance IPacking Bottle where
  pack Bottle = "Bottle"

data Packing = MkWrapper Wrapper | MkBottle Bottle
instance IPacking Packing where
  pack (MkWrapper Wrapper) = pack Wrapper
  pack (MkBottle Bottle)   = pack Bottle

data VegBurger = VegBurger 
instance IItem VegBurger where
  price VegBurger = 2.5
  name VegBurger = "Veg Burger"
  packing VegBurger = MkWrapper Wrapper

data ChickenBurger = ChickenBurger
instance IItem ChickenBurger where
  price ChickenBurger = 5.05
  name ChickenBurger = "Chicken Burger"
  packing ChickenBurger = MkWrapper Wrapper

data Coke = Coke
instance IItem Coke where
  price Coke = 3.0
  name Coke = "Coke"
  packing Coke = MkBottle Bottle

data Pepsi = Pepsi
instance IItem Pepsi where
  price Pepsi = 3.5
  name Pepsi = "Pepsi"
  packing Pepsi = MkBottle Bottle


main = do 
  let 
    vegBuilder = VegetarianMealBuilder (Meal [])
    cook =  makeMeal (MakeCook vegBuilder)
    vegMeal = getMeal (getBuilder cook)
    in 
      putStrLn "Veg Meal"     >>
      showItems vegMeal       >>
      putStr "Total Cost: "   >> 
      putStrLn (show (getCost vegMeal))
  let 
    nonVegBuilder = NonVegetarianMealBuilder (Meal [])
    cook =  makeMeal (MakeCook nonVegBuilder)
    nonVegMeal = getMeal (getBuilder cook)
    in 
      putStrLn "\nNon-Veg Meal"     >>
      showItems nonVegMeal       >>
      putStr "Total Cost: "   >> 
      putStrLn (show (getCost nonVegMeal))


    
