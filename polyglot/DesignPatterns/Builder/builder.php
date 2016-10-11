<?php
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

class DirectorCook {
  // A director is constructed from a builder, which specifies its toolbox
  public function __construct($builder){
    $this->builder = $builder;
  }

  // This is the main method of the director, which creates an object
  // based on some logic and algorithm which is encapsulated in the
  // method body, and uses the tools provided by the builder interface.
  public function makeMeal(){
    $this->builder->startNewMeal();
    $this->builder->addBurger();
    $this->builder->addDrink();
  }
  private $builder;
}

// Note that the manufacture algorithm contained in the director
// is very general and does not tell us anything about the type of
// the object being created, let alone its internal representation.

interface MealBuilder {
  public function startNewMeal();
  public function addBurger();
  public function addDrink();
}

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
class VegetarianMealBuilder implements MealBuilder {
  // MealBuilder interface implementation
  public function startNewMeal(){$this->meal = new Meal();}
  public function addBurger(){$this->meal->addItem(new VegBurger());}
  public function addDrink(){$this->meal->addItem(new Coke());}
  // the getObject method
  public function getMeal(){return $this->meal;}
  // the object being created step by step
  private $meal;
}

// Non-Vegetarian meal comes with pepsi...
class NonVegetarianMealBuilder implements MealBuilder {
  // MealBuilder interface implementation
  public function startNewMeal(){$this->meal = new Meal;}
  public function addBurger(){$this->meal->addItem(new ChickenBurger);}
  public function addDrink(){$this->meal->addItem(new Pepsi);}
  // the getObject method
  public function getMeal(){return $this->meal;}
  // the object being created step by step
  private $meal;
}

// Both of the above concrete builders happen to produce objects
// of the same type 'Meal' implemented as a list of 'Item'

class Meal {
  public function __construct(){
    $this->items = [];
  }
  // This method is crucially needed for the implementation of both builders
  public function addItem($item){$this->items[] = $item;}  
  // we define a few more methods to make this example more interesting
  public function getCost(){
    $cost = 0.0;
    foreach($this->items as $item){
      $cost = $cost + $item->price();
    }
    return $cost;
  }
  //
  public function showItems(){
    foreach($this->items as $item){
      echo 'Item : '.$item->name().', Packing : '.$item->packing()->pack().
           ', Price : '.$item->price().PHP_EOL;
    }
  }
}

// The Item interface comes here
interface Item {
  public function price();
  public function name();
  public function packing();
}


// Item relises on the 'Packing' interface
interface Packing {
  public function pack();
}

class Wrapper implements Packing {
  public function pack(){
    return "Wrapper";
  }
}

class Bottle implements Packing {
  public function pack(){
    return "Bottle";
  }
}

abstract class Burger implements Item {
  public function packing(){
    return new Wrapper;
  }
}

abstract class ColdDrink implements Item {
  public function packing(){
    return new Bottle;
  }
}


class VegBurger extends Burger {
  public function price(){ return 2.5; }
  public function name(){ return "Veg Burger"; }
}

class ChickenBurger extends Burger {
  public function price(){ return 5.05; }
  public function name(){ return "Chicken Burger"; }
}

class Coke extends ColdDrink {
  public function price(){ return 3.0; }
  public function name(){ return "Coke"; }
}

class Pepsi extends ColdDrink {
  public function price(){ return 3.5; }
  public function name(){ return "Pepsi"; }
}

// let's try everything out


// First we create the appropriate concrete builder
$vegBuilder = new VegetarianMealBuilder;
// Next we create a director which will use this builder
$cook = new DirectorCook($vegBuilder);
// Next we let the cook prepare the meal
$cook->makeMeal();
// Next we retrieve the object from the builder
$vegMeal = $vegBuilder->getMeal();
// outputting results
echo "Veg Meal\n";
$vegMeal->showItems();
echo "Total Cost: ".$vegMeal->getCost()."\n";

// same for non-vegetarian meal
$nonVegBuilder = new NonVegetarianMealBuilder;
$cook = new DirectorCook($nonVegBuilder);
$cook->makeMeal();
$nonVegMeal = $nonVegBuilder->getMeal();
// outputting results
echo "\nNon-Veg Meal\n";
$nonVegMeal->showItems();
echo "Total Cost: ".$nonVegMeal->getCost()."\n";

?>
