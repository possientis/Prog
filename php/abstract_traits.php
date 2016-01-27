<?php
// can be done in Java with default interface method
// and also in scala with traits

trait Hello {
  public function sayHelloWorld() {
    echo 'Hello'.$this->getWorld();
  }
  abstract public function getWorld();
}

class MyHelloWorld {
  private $world;
  use Hello;
  public function __construct($world){
    $this->world = $world;
  }

  public function getWorld() {
    return $this->world;
  }
}

$w = new MyHelloWorld(' world!');
$w->sayHelloWorld();




?>

