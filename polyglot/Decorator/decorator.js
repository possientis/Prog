// Decorator Design Pattern


// interface or abstract class of components
////////////////////////////////////////////////////////////////////////////////
//                                 Pizza                                      //
////////////////////////////////////////////////////////////////////////////////
function Pizza(){}

Pizza.prototype.getDescription = function(){
  throw "Pizza::getDescription is not implemented";
}

Pizza.prototype.getCost = function(){
  throw "Pizza::getCost is not implemented";
}

////////////////////////////////////////////////////////////////////////////////
//                               Plain Pizza                                  //
////////////////////////////////////////////////////////////////////////////////

// concrete component
function PlainPizza(){ Pizza.call(this); }

PlainPizza.prototype = Object.create(Pizza.prototype);
PlainPizza.prototype.getDescription = function(){ return "Plain pizza"; }
PlainPizza.prototype.getCost = function(){ return 3.0; }

// root abstract class of decorators implementing component interface
// a decorator object is therefore a component and will hold a 
// concrete component as data member. Default implementation
// achieved simply by forwarding 


////////////////////////////////////////////////////////////////////////////////
//                                PizzaDecorator                              //
////////////////////////////////////////////////////////////////////////////////

function PizzaDecorator(pizza) {
  Pizza.call(this);
  this.pizza = pizza;
}
PizzaDecorator.prototype = Object.create(Pizza.prototype);
Pizza.prototype.getDescription = function(){ return this.pizza.getDescription(); }
Pizza.prototype.getCost = function(){ return this.pizza.getCost(); }

////////////////////////////////////////////////////////////////////////////////
//                                WithExtraCheese                             //
////////////////////////////////////////////////////////////////////////////////

// first concrete decorator
function WithExtraCheese(pizza){ PizzaDecorator.call(this, pizza); }
WithExtraCheese.prototype = Object.create(PizzaDecorator.prototype);
WithExtraCheese.prototype.getDescription = function(){
  return this.pizza.getDescription() + " + extra cheese";
}
WithExtraCheese.prototype.getCost = function(){
    return this.pizza.getCost() + 0.5;
}

////////////////////////////////////////////////////////////////////////////////
//                                WithExtraOlives                             //
////////////////////////////////////////////////////////////////////////////////

// second concrete decorator
function WithExtraOlives(pizza){ PizzaDecorator.call(this, pizza); }
WithExtraOlives.prototype = Object.create(PizzaDecorator.prototype);
WithExtraOlives.prototype.getDescription = function(){
  return this.pizza.getDescription() + " + extra olives";
}
WithExtraOlives.prototype.getCost = function(){
    return this.pizza.getCost() + 0.7;
}

////////////////////////////////////////////////////////////////////////////////
//                              WithExtraAnchovies                            //
////////////////////////////////////////////////////////////////////////////////

// third concrete decorator
function WithExtraAnchovies(pizza){ PizzaDecorator.call(this, pizza); }
WithExtraAnchovies.prototype = Object.create(PizzaDecorator.prototype);
WithExtraAnchovies.prototype.getDescription = function(){
  return this.pizza.getDescription() + " + extra anchovies";
}
WithExtraAnchovies.prototype.getCost = function(){
    return this.pizza.getCost() + 0.8;
}


////////////////////////////////////////////////////////////////////////////////
//                                  Main                                      //
////////////////////////////////////////////////////////////////////////////////

plainPizza  = new PlainPizza();

nicePizza   = new WithExtraCheese(
              new PlainPizza()); 

superPizza  = new WithExtraOlives( 
              new WithExtraCheese(
              new PlainPizza())); 

ultraPizza  = new WithExtraAnchovies(
              new WithExtraOlives( 
              new WithExtraCheese(
              new PlainPizza()))); 

print(  "Plain Pizza: "   +
        "\tCost: "        + plainPizza.getCost().toFixed(1) // formatting
      + "\tDescription: " + plainPizza.getDescription()); 


print(  "Nice Pizza: "   +
        "\tCost: "        + nicePizza.getCost().toFixed(1)
      + "\tDescription: " + nicePizza.getDescription()); 

print(  "Super Pizza: "   +
        "\tCost: "        + superPizza.getCost().toFixed(1)
      + "\tDescription: " + superPizza.getDescription()); 

print(  "Ultra Pizza: "   +
        "\tCost: "        + ultraPizza.getCost().toFixed(1)
      + "\tDescription: " + ultraPizza.getDescription()); 


