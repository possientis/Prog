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

class DirectorCook(object):
    # A director is constructed from a builder, which specifies its toolbox
    def __init__(self, builder):
        self._builder = builder
    # This is the main method of the director, which creates an object
    # based on some logic and algorithm which is encapsulated in the
    # method body, and uses the tools provided by the builder interface.
    def makeMeal(self):
        self._builder.startNewMeal()
        self._builder.addBurger()
        self._builder.addDrink()
    
# Note that the manufacture algorithm contained in the director
# is very general and does not tell us anything about the type of
# the object being created, let alone its internal representation.

class MealBuilder(object):
    def startNewMeal(self):
        raise NotImplemented
    def addBurger(self):
        raise NotImplemented
    def addDrink(self):
        raise NotImplemented

# We can implement MealBuilder in many different ways, so as to 
# construct objects of many possible types which do not even need
# to be related by a common base class 'Meal' or anything beyond 'object'

# However, at some point we need to retrieve the constructed object
# so there must be some method 'getObject'. In general, because the
# return type of 'getObject' may be arbitrary, the method declaration
# cannot be part of the interface MealBuilder as this would constrain
# the implementation to a specific type being constructed.

# In this example, we shall consider two concrete implementations of
# MealBuilder, a 'VegetarianMealBuilder' and a 'NonVegetarianMealBuilder'.
# Both implementation will allow the construction of objects of the same
# type, but one should remember that this need not be the case when 
# applying the builder design pattern.

# Concrete implementations of MealBuilder will hold an object of type
# Meal (the object being constructed), and will have a getObject() method.

class VegetarianMealBuilder(MealBuilder):
    def startNewMeal(self):
        self._meal = Meal()
    def addBurger(self):
        self._meal.addItem(VegBurger())
    def addDrink(self):
        self._meal.addItem(Coke())
    # the getObject method
    def getMeal(self):
        return self._meal

class NonVegetarianMealBuilder(MealBuilder):
    def startNewMeal(self):
        self._meal = Meal()
    def addBurger(self):
        self._meal.addItem(ChickenBurger())
    def addDrink(self):
        self._meal.addItem(Pepsi())
    # the getObject method
    def getMeal(self):
        return self._meal

# Both of the above concrete builders happen to produce objects
# of the same type 'Meal' implemented as a list of 'Item'
class Meal(object):
    def __init__(self):
        self._items = []
    def addItem(self,item):
        self._items.append(item)
    def getCost(self):
        cost = 0.0
        for item in self._items:
            cost += item.price()
        return cost
    def showItems(self):
        for item in self._items:
            print('Item : ' + item.name(), end="")
            print(', Packing : ' + item.packing().pack(), end="")
            print(', Price : ' + str(item.price()))

# The item interface comes here
class Item(object):
    def price(self):
        raise NotImplemented
    def name(self):
        raise NotImplemented
    def packing(self):
        raise NotImplemented

# Item relies on the 'Packing' interface
class Packing(object):
    def pack(self):
        raise NotImplemented

class Wrapper(Packing):
    def pack(self):
        return 'Wrapper'
class Bottle(Packing):
    def pack(self):
        return 'Bottle'

class Burger(Item):
    def packing(self):
        return Wrapper()

class ColdDrink(Item):
    def packing(self):
        return Bottle()

class VegBurger(Burger):
    def price(self):
        return 2.5
    def name(self):
        return 'Veg Burger'

class ChickenBurger(Burger):
    def price(self):
        return 5.05
    def name(self):
        return 'Chicken Burger'


class Coke(ColdDrink):
    def price(self):
        return 3.0
    def name(self):
        return 'Coke'

class Pepsi(ColdDrink):
    def price(self):
        return 3.5
    def name(self):
        return 'Pepsi'



# creating vegetarian meal
# First we create the appropriate concrete builder
vegBuilder = VegetarianMealBuilder()
# Next we create a director which will use this builder
cook = DirectorCook(vegBuilder)
# Next we let the cook prepare the meal
cook.makeMeal()
# Next we retrieve the object from the builder
vegMeal = vegBuilder.getMeal()
# outputting result
print('Veg Meal')
vegMeal.showItems()
print('Total Cost: ' + str(vegMeal.getCost()));
#
# same for non-vegetarian meal
nonVegBuilder = NonVegetarianMealBuilder();
cook = DirectorCook(nonVegBuilder);
cook.makeMeal();
nonVegMeal = nonVegBuilder.getMeal();
# outputting result
print('\nNon-Veg Meal')
nonVegMeal.showItems()
print('Total Cost: ' + str(nonVegMeal.getCost()));


