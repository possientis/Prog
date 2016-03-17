// Decorator Design Pattern
using System;

// interface or abstract class of components
interface Pizza {
  string Description { get; }
  double Cost { get; }
}

// concrete component
class PlainPizza : Pizza {
  public PlainPizza(){}
  public string Description { get { return "Plain pizza"; } }
  public double Cost { get { return 3.0; } }
}

// root abstract class of decorators implementing component interface
// a decorator object is therefore a component and will hold a 
// concrete component as data member. Default implementation
// achieved simply by forwarding 

abstract class PizzaDecorator : Pizza {

  protected readonly Pizza _pizza;

  public PizzaDecorator(Pizza pizza){ _pizza = pizza; }

  // default implementation
  public virtual string Description { get { return _pizza.Description; } }
  // default implementation
  public virtual double Cost { get { return _pizza.Cost; } }

}

// first concrete decorator
class WithExtraCheese : PizzaDecorator {

  public WithExtraCheese(Pizza pizza) : base(pizza) {}

  public override string Description { get {
    return _pizza.Description + " + extra cheese";
  }}

  public override double Cost { get {
    return _pizza.Cost + 0.5;
  }}
}

// second concrete decorator
class WithExtraOlives : PizzaDecorator {

  public WithExtraOlives(Pizza pizza) : base(pizza) {}

  public override string Description { get {
    return _pizza.Description + " + extra olives";
  }}

  public override double Cost { get {
    return _pizza.Cost + 0.7;
  }}
}

// third concrete decorator
class WithExtraAnchovies : PizzaDecorator {

  public WithExtraAnchovies(Pizza pizza) : base(pizza) {}

  public override string Description { get {
    return _pizza.Description + " + extra anchovies";
  }}

  public override double Cost { get {
    return _pizza.Cost + 0.8;
  }}
}


public class Decorator{

  public static void Main(string[] args){

    Pizza plainPizza  = new PlainPizza();

    Pizza nicePizza   = new WithExtraCheese(
                        new PlainPizza());

    Pizza superPizza  = new WithExtraOlives(
                        new WithExtraCheese(
                        new PlainPizza()));

    Pizza ultraPizza  = new WithExtraAnchovies(
                        new WithExtraOlives(
                        new WithExtraCheese(
                        new PlainPizza())));

    Console.WriteLine(
        "Plain Pizza: \tCost: {0:0.0} \tDescription: {1}",
         plainPizza.Cost, plainPizza.Description); 

    Console.WriteLine(
        "Nice Pizza: \tCost: {0:0.0} \tDescription: {1}",
         nicePizza.Cost, nicePizza.Description); 

    Console.WriteLine(
        "Super Pizza: \tCost: {0:0.0} \tDescription: {1}",
         superPizza.Cost, superPizza.Description); 

    Console.WriteLine(
        "Ultra Pizza: \tCost: {0:0.0} \tDescription: {1}",
         ultraPizza.Cost, ultraPizza.Description); 
  }

}
