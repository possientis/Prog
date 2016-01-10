// Builder Design Pattern

// The main idea behind the builder design pattern is
// to provide an abstract interface for a 'builder object'
// A concrete builder object is not a factory object which returns
// a ready-made object of a certain type. A concrete builder object
// should be viewed as a toolbox allowing someone else (that someone
// else is called 'a director' within the context of the builer design
// pattern) to build an object of some type according to some plan.

// Let us define a possible 'director' class, whose purpose
// it is to manufacture meals


// A director is constructed from a builder, which specifies its toolbox
class DirectorCook(builder: MealBuilder) {

  // This is the main method of the director, which creates an object
  // based on some logic and algorithm which is encapsulated in the
  // method body, and uses the tools provided by the builder interface.
  def makeMeal() = {
    builder.startNewMeal()
    builder.addBurger()
    builder.addDrink()
  }
}

// Note that the manufacture algorithm contained in the director
// is very general and does not tell us anything about the type of
// the object being created, let alone its internal representation.

abstract class MealBuilder {
  def startNewMeal()
  def addBurger()
  def addDrink()
}

// We can implement MealBuilder in many different ways, so as to 
// construct objects of many possible types which do not even need
// to be related by a common base class 'Meal' or anything beyond 'Any'

// However, at some point we need to retrieve the constructed object
// so there must be some method 'getObject'. In general, because the
// return type of 'getObject' may be arbitrary, the method declaration
// cannot be part of the interface MealBuilder as this would constrain
// the implementation to a specific type being constructed.

// In this example, we shall consider two concrete implementations of
// MealBuilder, a 'VegetarianMealBuilder' and a 'NonVegetarianMealBuilder'.
// Both implementation will allow the construction of objects of the same
// type, but one should remember that this need not be the case when 
// applying the builder design pattern.

// Concrete implementations of MealBuilder will hold an object of type
// Meal (the object being constructed), and will have a getObject() method.

// Vegetarian meal comes with coke for some reason
class VegetarianMealBuilder extends MealBuilder {
  // the object being created step by step
  var _meal: Meal = null
  // MealBuilder interface implementation
  def startNewMeal() = {_meal = new Meal}
  def addBurger() = {_meal.addItem(new VegBurger)}
  def addDrink() = {_meal.addItem(new Coke)}
  // the getObject method
  def getMeal(): Meal = _meal
}

class NonVegetarianMealBuilder extends MealBuilder {
  // the object being created step by step
  var _meal: Meal = null
  // MealBuilder interface implementation
  def startNewMeal() = {_meal = new Meal}
  def addBurger() = {_meal.addItem(new ChickenBurger)}
  def addDrink() = {_meal.addItem(new Pepsi)}
  // the getObject method
  def getMeal(): Meal = _meal
}

class Meal {
  var _items : List[Item] = Nil
  // This method is crucially needed for the implementation of both builders
  def addItem(item: Item) = {_items = item :: _items}
  // we define a few more methods to make this example more interesting
  def getCost(): Double = {
    def add(sum: Double, item: Item) = sum + item.price()
    return _items.foldLeft(0.0)(add) 
  } 
  def showItems() = {
    def display(item: Item) = {
      print("Item: " + item.name())
      print(", Packing : " + item.packing().pack())
      println(", Price : " + item.price())
    }
    _items.map(display)
  }
}


// The Item interface comes here
abstract class Item {
  def price(): Double
  def name(): String
  def packing(): Packing
}

// Item relies on the 'Packing' interface
abstract class Packing {
  def pack(): String
}

class Wrapper extends Packing {
  def pack() = "Wrapper"
}

class Bottle extends Packing {
  def pack() = "Bottle"
}

abstract class Burger extends Item {
  def packing() = new Wrapper
}

abstract class ColdDrink extends Item {
  def packing() = new Bottle
}

class VegBurger extends Burger {
  def price() = 2.5
  def name() = "Veg Burger"
}

class ChickenBurger extends Burger {
  def price() = 5.05 
  def name() = "Chicken Burger"
}

class Coke extends ColdDrink {
  def price() = 3.0 
  def name() = "Coke"
}

class Pepsi extends ColdDrink {
  def price() = 3.5 
  def name() = "Pepsi"
}


object Builder {
  def main(args: Array[String]) = {
    // creating vegetarian meal
    // First we create the appropriate concrete builder
    val vegBuilder = new VegetarianMealBuilder 
    // Next we create a director which will use this builder
    var cook = new DirectorCook(vegBuilder)
    // Next we let the cook prepare the meal
    cook.makeMeal()
    // Next we retrieve the object from the builder
    val vegMeal = vegBuilder.getMeal()
    // outputting results
    println("Veg Meal")
    vegMeal.showItems()
    println("TotalCost: " + vegMeal.getCost())

    // same for non-vegetarian meal
    val nonVegBuilder = new NonVegetarianMealBuilder 
    // Next we create a director which will use this builder
    cook = new DirectorCook(nonVegBuilder)
    // Next we let the cook prepare the meal
    cook.makeMeal()
    // Next we retrieve the object from the builder
    val nonVegMeal = nonVegBuilder.getMeal()
    // outputting results
    println("\nNon-Veg Meal")
    nonVegMeal.showItems()
    println("TotalCost: " + nonVegMeal.getCost())
  }
}


