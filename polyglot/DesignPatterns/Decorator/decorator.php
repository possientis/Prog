<?php
// Decorator Design Pattern

// The implementation of the decorator pattern in php does not follow
// the pattern encountered in other languages, due to php built in 'traits'

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

trait WithExtraOlives {
  public function description(){ 
    return parent::description()." + extra olives";
  }
  public function cost(){ 
    return parent::cost() + 0.7; 
  }
}

trait WithExtraAnchovies {
  public function description(){ 
    return parent::description()." + extra anchovies";
  }
  public function cost(){ 
    return parent::cost() + 0.8; 
  }
}

class NicePizza extends PlainPizza {
  use WithExtraCheese;
}

class SuperPizza extends NicePizza {
  use WithExtraOlives;
}

class UltraPizza extends SuperPizza {
  use WithExtraAnchovies;
}

$plainPizza = new PlainPizza();
$nicePizza  = new NicePizza();
$superPizza = new SuperPizza();
$ultraPizza = new UltraPizza();

echo  "Plain Pizza: "   .
      "\tCost: "        . number_format($plainPizza->cost(), 1).
      "\tDescription: " . $plainPizza->description()."\n"; 

echo  "Nice Pizza: "    .
      "\tCost: "        . number_format($nicePizza->cost(), 1).
      "\tDescription: " . $nicePizza->description()."\n"; 

echo  "Super Pizza: "   .
      "\tCost: "        . number_format($superPizza->cost(), 1).
      "\tDescription: " . $superPizza->description()."\n"; 

echo  "Ultra Pizza: "   .
      "\tCost: "        . number_format($ultraPizza->cost(), 1).
      "\tDescription: " . $ultraPizza->description()."\n"; 


?>
