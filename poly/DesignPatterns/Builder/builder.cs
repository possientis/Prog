// Builder Design Pattern
using System;
using System.Collections.Generic;

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
  public DirectorCook(IMealBuilder builder) 
  {
    _builder = builder;
  }

  // This is the main method of the director, which creates an object
  // based on some logic and algorithm which is encapsulated in the
  // method body, and uses the tools provided by the builder interface.
  public void MakeMeal(){
    _builder.StartNewMeal();
    _builder.AddBurger();
    _builder.AddDrink();
  }
  private IMealBuilder _builder;
}

// Note that the manufacture algorithm contained in the director
// is very general and does not tell us anything about the type of
// the object being created, let alone its internal representation.

interface IMealBuilder{
  void StartNewMeal();
  void AddBurger();
  void AddDrink();
}

// We can implement IMealBuilder in many different ways, so as to 
// construct objects of many possible types which do not even need
// to be related by a common base class 'Meal' or anything beyond 'object'

// However, at some point we need to retrieve the constructed object
// so there must be some method 'GetObject'. In general, because the
// return type of 'GetObject' may be arbitrary, the method declaration
// cannot be part of the interface IMealBuilder as this would constrain
// the implementation to a specific type being constructed.

// In this example, we shall consider two concrete implementations of
// IMealBuilder, a 'VegetarianMealBuilder' and a 'NonVegetarianMealBuilder'.
// Both implementation will allow the construction of objects of the same
// type, but one should remember that this need not be the case when 
// applying the builder design pattern.

// Concrete implementations of IMealBuilder will hold an object of type
// Meal (the object being constructed), and will have a GetObject() method.

// Vegetarian meal comes with 'coke' for some reason
class VegetarianMealBuilder : IMealBuilder {
  // MealBuilder interface implementation
  public void StartNewMeal(){_meal = new Meal();}
  public void AddBurger(){_meal.AddItem(new VegBurger());}
  public void AddDrink(){_meal.AddItem(new Coke());}
  // the GetObject method
  public Meal GetMeal(){return _meal;}
  // the object being created step by step
  private Meal _meal;
}

// Non-vegetarian meal comes with 'pepsi'...
class NonVegetarianMealBuilder : IMealBuilder {
   // MealBuilder interface implementation
  public void StartNewMeal(){_meal = new Meal();}
  public void AddBurger(){_meal.AddItem(new ChickenBurger());}
  public void AddDrink(){_meal.AddItem(new Pepsi());}
  // the GetObject method
  public Meal GetMeal(){return _meal;}
  // the object being created step by step
  private Meal _meal;
}

// Both of the above concrete builders happen to produce objects
// of the same type 'Meal' implemented as a list of 'Item'
class Meal{
  public Meal(){_items = new List<Item>();}
  // This method is crucially needed for the implementation of both builders
  public void AddItem(Item item){_items.Add(item);}
  // we define a few more methods to make this example more interesting
  public double GetCost(){
    double cost = 0.0;
    foreach(Item item in  _items){
      cost += item.Price();
    }
    return cost;
  }
  //
  public void ShowItems(){
    foreach(Item item in _items){
      Console.Write("Item : " + item.Name());
      Console.Write(", Packing : " + item.Packing().Pack());
      Console.WriteLine(", Price : " + item.Price());
    }
  }
  // data
  private IList<Item> _items;
}

// The Item interface comes here (we do not call it 'IItem')
interface Item {
  double Price();
  String Name();
  Packing Packing();
}

// Item relies on the 'Packing' interface
interface Packing {
  String Pack();
}

class Wrapper : Packing {
  public String Pack(){return "Wrapper";}
}

class Bottle : Packing {
  public String Pack(){return "Bottle";}
}

abstract class Burger : Item {
  public Packing Packing(){return new Wrapper();}
  public abstract string Name();
  public abstract double Price();
}

abstract class ColdDrink : Item {
  public Packing Packing(){return new Bottle();}
  public abstract string Name();
  public abstract double Price();
}

class VegBurger : Burger {
  public override double Price(){return 2.5;}
  public override String Name(){return "Veg Burger";}
}

class ChickenBurger : Burger {
  public override double Price(){return 5.05;}
  public override String Name(){return "Chicken Burger";}
}

class Coke : ColdDrink {
  public override double Price(){return 3.0;}
  public override String Name(){return "Coke";}
}

class Pepsi : ColdDrink {
  public override double Price(){return 3.5;}
  public override String Name(){return "Pepsi";}
}

// let's try everything out
public class Builder{

  public static void Main(string[] args){
    // creating vegetarian meal
    // First we create the appropriate concrete builder
    VegetarianMealBuilder vegBuilder = new VegetarianMealBuilder();
    // Next we create a director which will use this builder
    DirectorCook cook = new DirectorCook(vegBuilder);
    // Next we let the cook prepare the meal
    cook.MakeMeal();
    // Next we retrieve the object from the builder
    // Note here that we needed to declare vegBuilder specifically
    // of type 'VegetarianMealBuilder', rather than 'IMealBuilder'
    // so we have access to the method 'GetMeal' which is not part
    // of the 'IMealBuilder' interface. Because both our concrete
    // builders in this example create objects of the same type
    // 'Meal', it is of course possible to declare GetMeal as 
    // part of the IMealBuilder interface. 
    Meal vegMeal = vegBuilder.GetMeal();
    // outputting result
    Console.WriteLine("Veg Meal");
    vegMeal.ShowItems();
    Console.WriteLine("Total Cost: " + vegMeal.GetCost());

    // same for non-vegetarian meal
    NonVegetarianMealBuilder nonVegBuilder = new NonVegetarianMealBuilder();
    cook = new DirectorCook(nonVegBuilder);
    cook.MakeMeal();
    Meal nonVegMeal = nonVegBuilder.GetMeal();
    // outputting result
    Console.WriteLine("\nNon-Veg Meal");
    nonVegMeal.ShowItems();
    Console.WriteLine("Total Cost: " + nonVegMeal.GetCost());
  }
}
