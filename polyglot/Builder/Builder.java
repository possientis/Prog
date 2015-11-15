// Builder Design Pattern
import java.util.List; // List<E>
import java.util.ArrayList; // ArrayList<E>

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
  // A director is contructed from a builder, which specifies its toolbox
  public DirectorCook(MealBuilder builder) 
  {
    _builder = builder;
  }

  // This is the main method of the director, which creates an object
  // based on some logic and algorithm which is encapsulated in the
  // method body, and uses the tools provided by the builder interface.
  public void makeMeal(){
    _builder.startNewMeal();
    _builder.addBurger();
    _builder.addDrink();
  }
  private MealBuilder _builder;
}

// Note that the manufacture algorithm contained in the director
// is very general and does not tell us anything about the type of
// the object being created, let alone its internal representation.

interface MealBuilder{
  void startNewMeal();
  void addBurger();
  void addDrink();
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
  public void startNewMeal(){_meal = new Meal();}
  public void addBurger(){_meal.addItem(new VegBurger());}
  public void addDrink(){_meal.addItem(new Coke());}
  // the getObject method
  public Meal getMeal(){return _meal;}
  // the object being created step by step
  private Meal _meal;
}

// Non-vegetarian meal comes with pepsi...
class NonVegetarianMealBuilder implements MealBuilder {
   // MealBuilder interface implementation
  public void startNewMeal(){_meal = new Meal();}
  public void addBurger(){_meal.addItem(new ChickenBurger());}
  public void addDrink(){_meal.addItem(new Pepsi());}
  // the getObject method
  public Meal getMeal(){return _meal;}
  // the object being created step by step
  private Meal _meal;
}

// Both of the above concrete builders happen to produce objects
// of the same type 'Meal' implemented as a list of 'Item'
class Meal{
  public Meal(){_items = new ArrayList<Item>();}
  // This method is crucially needed for the implementation of both builders
  public void addItem(Item item){_items.add(item);}
  // we define a few more methods to make this example more interesting
  public double getCost(){
    double cost = 0.0;
    for(Item item : _items){
      cost += item.price();
    }
    return cost;
  }
  //
  public void showItems(){
    for(Item item : _items){
      System.out.print("Item : " + item.name());
      System.out.print(", Packing : " + item.packing().pack());
      System.out.println(", Price : " + item.price());
    }
  }
  // data
  private List<Item> _items;
}

// The Item interface comes here
interface Item {
  double price();
  String name();
  Packing packing();
}

// Item relies on the 'Packing' interface
interface Packing {
  String pack();
}

class Wrapper implements Packing {
  @Override
  public String pack(){return "Wrapper";}
}

class Bottle implements Packing {
  @Override
  public String pack(){return "Bottle";}
}

abstract class Burger implements Item {
  @Override
  public Packing packing(){return new Wrapper();}
}

abstract class ColdDrink implements Item {
  @Override
  public Packing packing(){return new Bottle();}
}

class VegBurger extends Burger {
  @Override
  public double price(){return 2.5;}
  @Override
  public String name(){return "Veg Burger";}
}

class ChickenBurger extends Burger {
  @Override
  public double price(){return 5.05;}
  @Override
  public String name(){return "Chicken Burger";}
}

class Coke extends ColdDrink {
  @Override
  public double price(){return 3.0;}
  @Override
  public String name(){return "Coke";}
}

class Pepsi extends ColdDrink {
  @Override
  public double price(){return 3.5;}
  @Override
  public String name(){return "Pepsi";}
}

// let's try everything out
public class Builder{

  public static void main(String[] args){
    // creating vegetarian meal
    // First we create the appropriate concrete builder
    VegetarianMealBuilder vegBuilder = new VegetarianMealBuilder();
    // Next we create a director which will use this builder
    DirectorCook cook = new DirectorCook(vegBuilder);
    // Next we let the cook prepare the meal
    cook.makeMeal();
    // Next we retrieve the object from the builder
    // Note here that we needed to declare vegBuilder specifically
    // of type 'VegetarianMealBuilder', rather than 'MealBuilder'
    // so we have access to the method 'getMeal' which is not part
    // of the 'MealBuilder' interface. Because both our concrete
    // builders in this example create objects of the same type
    // 'Meal', it is of course possible to declare getMeal as 
    // part of the MealBuilder interface. 
    Meal vegMeal = vegBuilder.getMeal();
    // outputting result
    System.out.println("Veg Meal");
    vegMeal.showItems();
    System.out.println("Total Cost: " + vegMeal.getCost());

    // same for non-vegetarian meal
    NonVegetarianMealBuilder nonVegBuilder = new NonVegetarianMealBuilder();
    cook = new DirectorCook(nonVegBuilder);
    cook.makeMeal();
    Meal nonVegMeal = nonVegBuilder.getMeal();
    // outputting result
    System.out.println("\nNon-Veg Meal");
    nonVegMeal.showItems();
    System.out.println("Total Cost: " + nonVegMeal.getCost());
  }
}
