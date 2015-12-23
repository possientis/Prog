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

function DirectorCook(builder){
  this._builder = builder;
};

// This is the main method of the director, which creates an object
// based on some logic and algorithm which is encapsulated in the
// method body, and uses the tools provided by the builder interface.

DirectorCook.prototype.makeMeal = function(){
  this._builder.startNewMeal();
  this._builder.addBurger();
  this._builder.addDrink();
}

// Note that the manufacture algorithm contained in the director
// is very general and does not tell us anything about the type of
// the object being created, let alone its internal representation.

function MealBuilder(){
};

MealBuilder.prototype.startNewMeal = function(){
  print("MealBuilder::startNewMeal is not implemented");
};

MealBuilder.prototype.addBurger = function(){
  print("MealBuilder::addBurger is not implemented");
};

MealBuilder.prototype.addDrink = function(){
  print("MealBuilder::addDrink is not implemented");
};

// We can implement MealBuilder in many different ways, so as to 
// construct objects of many possible types which do not even need
// to be related by a common base class 'Meal' or anything beyond 'Object'

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
function VegetarianMealBuilder(){
  MealBuilder.call(this);
  this._meal = null;
};

VegetarianMealBuilder.prototype = Object.create(MealBuilder.prototype);
VegetarianMealBuilder.prototype.startNewMeal = function(){
  this._meal = new Meal();
};

VegetarianMealBuilder.prototype.addBurger = function(){
  this._meal.addItem(new VegBurger());
}

VegetarianMealBuilder.prototype.addDrink = function(){
  this._meal.addItem(new Coke());
};

VegetarianMealBuilder.prototype.getMeal = function(){
  return _meal;
};

// Non-vegetarian meal comes with pepsi...
function NonVegetarianMealBuilder(){
  MealBuilder.call(this);
  this._meal = null;
};

NonVegetarianMealBuilder.prototype = Object.create(MealBuilder.prototype);
NonVegetarianMealBuilder.prototype.startNewMeal = function(){
  this._meal = new Meal();
};

NonVegetarianMealBuilder.prototype.addBurger = function(){
  this._meal.addItem(new ChickenBurger());
}

NonVegetarianMealBuilder.prototype.addDrink = function(){
  this._meal.addItem(new Pepsi());
};

NonVegetarianMealBuilder.prototype.getMeal = function(){
  return _meal;
};


// Both of the above concrete builders happen to produce objects
// of the same type 'Meal' implemented as a list of 'Item'

function Meal(){
  this._items = new Array();
  this._count = 0;
};

Meal.prototype.addItem = function(item){
  this._items[this._count] = item;
  ++this._count;
};

Meal.prototype.getCost = function(){
  var cost = 0.0;
  for(i = 0; i < this._count; ++i){
    cost += this._items[i].price();
  }
  return cost;
};

Meal.prototype.showItems = function(){
  for(i =0; i < this._count; ++i){
    item = this._items[i];
    print("Item : " + item.name() + ", Packing : " + item.packing().pack()
        + ", Price : " + item.price());
  }
};


// The Item interface comes here
function Item(){
};

Item.prototype.price = function(){
  print("Item::price is not implemented");
};

Item.prototype.name = function(){
  print("Item::name is not implemented");
};

Item.prototype.packing = function(){
  print("Item::packing is not implemented");
}












