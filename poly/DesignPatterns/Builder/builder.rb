# Builder Design Pattern

# The main idea behind the builder design pattern is
# to provide an abstract interface for a 'builder object'
# A concrete builder object is not a factory object which returns
# a ready-made object of a certain type. A concrete builder object
# should be viewed as a toolbox allowing someone else (that someone
# else is called 'a director' within the context of the builer design
# pattern) to build an object of some type according to some plan.

# Let us define a possible 'director' class, whose purpose
# it is to manufacture meals

class DirectorCook
  # A director is constructed from a builder, which specifies its toolbox
  def initialize(builder)
    @builder = builder
  end

  # This is the main method of the director, which creates an object
  # based on some logic and algorithm which is encapsulated in the
  # method body, and uses the tools provided by the builder interface.
  def makeMeal
    @builder.startNewMeal
    @builder.addBurger
    @builder.addDrink
  end
end


# Note that the manufacture algorithm contained in the director
# is very general and does not tell us anything about the type of
# the object being created, let alone its internal representation.

class MealBuilder
  def startNewMeal
    raise Exception.new "MealBuilder::startNewMeal is not implemented"
  end
  def addBurger
    raise Exception.new "MealBuilder::addBurger is not implemented"
  end
  def addDrink
    raise Exception.new "MealBuilder::addDrink is not implemented"
  end
end

# We can implement MealBuilder in many different ways, so as to 
# construct objects of many possible types which do not even need
# to be related by a common base class 'Meal' or anything beyond 'Object'
#
# However, at some point we need to retrieve the constructed object
# so there must be some method 'getObject'. In general, because the
# return type of 'getObject' may be arbitrary, the method declaration
# cannot be part of the interface MealBuilder as this would constrain
# the implementation to a specific type being constructed.
#
# In this example, we shall consider two concrete implementations of
# MealBuilder, a 'VegetarianMealBuilder' and a 'NonVegetarianMealBuilder'.
# Both implementation will allow the construction of objects of the same
# type, but one should remember that this need not be the case when 
# applying the builder design pattern.
#
# Concrete implementations of MealBuilder will hold an object of type
# Meal (the object being constructed), and will have a getObject() method.

# Vegetarian meal comes with coke for some reason
class VegetarianMealBuilder < MealBuilder
  def initialize
    @meal = nil
  end
  def startNewMeal
    @meal = Meal.new
  end
  def addBurger
    @meal.addItem VegBurger.new
  end
  def addDrink
    @meal.addItem Coke.new
  end
  # the getObject method
  def getMeal
    return @meal
  end
end

# Non-Vegetarian meal comes with pepsi...
class NonVegetarianMealBuilder < MealBuilder
  def initialize
    @meal = nil
  end
  def startNewMeal
    @meal = Meal.new
  end
  def addBurger
    @meal.addItem ChickenBurger.new
  end
  def addDrink
    @meal.addItem Pepsi.new
  end
  # the getObject method
  def getMeal
    return @meal
  end
end

# Both of the above concrete builders happen to produce objects
# of the same type 'Meal' implemented as a list of 'Item'
class Meal
  def initialize
    @items = []
  end
  # This method is crucially needed for the implementation of both builders
  def addItem(item)
    @items[@items.length] = item
  end
  # We define a few more methods to make this example more interesting
  def getCost
    @items.inject(0.0) {|sum, item| sum + item.price} # inject = FoldL
  end
  def showItems
    @items.each do |item|
      puts "Item: #{item.name}, Packing : #{item.packing.pack}" +
           ", Price : #{item.price}"
    end
  end
end

class Item
  def price
    raise Exception.new "Item::price is not implemented"
  end
  def name
    raise Exception.new "Item::name is not implemented"
  end
  def packing
    raise Exception.new "Item::packing is not implemented"
  end
end

class Packing
  def pack
    raise Exception.new "Packing::pack is not implemented"
  end
end

class Wrapper < Packing
  def pack
    "Wrapper" 
  end
end

class Bottle < Packing
  def pack
    "Bottle" 
  end
end

class Burger < Item
  def packing
    Wrapper.new
  end
end

class ColdDrink < Item
  def packing
    Bottle.new
  end
end

class VegBurger < Burger
  def price
    2.5
  end
  def name
    "Veg Burger"
  end
end

class ChickenBurger < Burger
  def price
    5.05
  end
  def name
    "Chicken Burger"
  end
end

class Coke < ColdDrink
  def price
    3.0
  end
  def name
    "Coke"
  end
end

class Pepsi < ColdDrink
  def price
    3.5
  end
  def name
    "Pepsi"
  end
end

# let's try everything out

# Creating vegetarian meal
# First we create the appropriate concrete builder
vegBuilder = VegetarianMealBuilder.new
# Next we create a director which will use this builder
cook = DirectorCook.new(vegBuilder)
# Next we let the cook prepare the meal
cook.makeMeal
# Next we retrieve the meal from the builder
vegMeal = vegBuilder.getMeal
# outputting results
puts "Veg meal"
vegMeal.showItems
puts "Total Cost: #{vegMeal.getCost}"

# same for non-vegetarian meal
nonVegBuilder = NonVegetarianMealBuilder.new
cook = DirectorCook.new(nonVegBuilder)
cook.makeMeal
nonVegMeal = nonVegBuilder.getMeal
# outputting results
puts "\nNon-Veg meal"
nonVegMeal.showItems
puts "Total Cost: #{nonVegMeal.getCost}"








