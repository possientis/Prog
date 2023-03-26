// Decorator Design Pattern

// interface or abstract class of components
interface Pizza {
  public String getDescription();
  public double getCost();
}

// concrete component
class PlainPizza implements Pizza {
  public PlainPizza(){}
  @Override 
  public String getDescription(){ return "Plain pizza"; }

  @Override
  public double getCost(){ return 3.0; }
} 


// root abstract class of decorators implementing component interface
// a decorator object is therefore a component and will hold a 
// concrete component as data member. Default implementation
// achieved simply by forwarding 

abstract class PizzaDecorator implements Pizza {

  protected final Pizza _pizza;

  public PizzaDecorator(Pizza pizza){ _pizza = pizza; }

  @Override   // default implementation
  public String getDescription(){ return _pizza.getDescription(); }

  @Override   // default implementation
  public double getCost(){ return _pizza.getCost(); }

}


// first concrete decorator 
class WithExtraCheese extends PizzaDecorator {

  public WithExtraCheese(Pizza pizza){ super(pizza); }

  @Override
  public String getDescription(){ 
    return _pizza.getDescription() + " + extra cheese";
  }

  @Override
  public double getCost(){ return _pizza.getCost() + 0.5; }

}

// second concrete decorator
class WithExtraOlives extends PizzaDecorator {

  public WithExtraOlives(Pizza pizza){ super(pizza); }

  @Override
  public String getDescription(){ 
    return _pizza.getDescription() + " + extra olives";
  }

  @Override
  public double getCost(){ return _pizza.getCost() + 0.7; }

}

// third concrete decorator
class WithExtraAnchovies extends PizzaDecorator {

  public WithExtraAnchovies(Pizza pizza){ super(pizza); }

  @Override
  public String getDescription(){ 
    return _pizza.getDescription() + " + extra anchovies";
  }

  @Override
  public double getCost(){ return _pizza.getCost() + 0.8; }

}

public class Decorator{

  public static void main(String[] args){

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

    System.out.println(
        "Plain Pizza: "   +
        "\tCost: "        + plainPizza.getCost() 
      + "\tDescription: " + plainPizza.getDescription());

    System.out.println(
        "Nice Pizza: "    +
        "\tCost: "        + nicePizza.getCost() 
      + "\tDescription: " + nicePizza.getDescription());

    System.out.println(
        "Super Pizza: "   +
        "\tCost: "        + superPizza.getCost() 
      + "\tDescription: " + superPizza.getDescription());

    System.out.println(
        "Ultra Pizza: "   +
        "\tCost: "        + ultraPizza.getCost() 
      + "\tDescription: " + ultraPizza.getDescription());

  }
}
