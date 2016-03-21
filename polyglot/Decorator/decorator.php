<?php
// Decorator Design Pattern

interface Pizza {
  public function description();
  public function cost();
}

class PlainPizza implements Pizza {
  public function description(){ return "Plain Pizza"; }
  public function cost(){ return 3.0; }
}


trait WithExtraCheese {
  public function description(){ 
    return parent::description()." + extra cheese";
  }
  public function cost(){ 
    return parent::cost() + 0.5; 
  }
}

class PizzaWithExtraCheese extends PlainPizza {
  use WithExtraCheese;
}

$plainPizza = new PlainPizza();
$nicePizza  = new PizzaWithExtraCheese();
echo $plainPizza->description()." ".$plainPizza->cost()."\n";
echo $nicePizza->description()." ".$nicePizza->cost()."\n";




















?>
