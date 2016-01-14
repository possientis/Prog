<?php
// Bridge design pattern

// bridge implementation interface
interface DrawAPI {
  public function drawCircle($radius, $x, $y);
}

// concrete bridge implementation classes implementing DrawAPI interface
class RedCircle implements DrawAPI {
  public function drawCircle($radius, $x, $y){
    echo "Drawing Circle[ color: red  , radius: $radius, x: $x, y: $y]\n";
  }
}

class GreenCircle implements DrawAPI {
  public function drawCircle($radius, $x, $y){
    echo "Drawing Circle[ color: green, radius: $radius, x: $x, y: $y]\n";
  }
}

// create an abstract class Shape using the DrawAPI interface.
abstract class Shape {
  protected $drawAPI;
  protected function __construct($drawAPI){
    $this->drawAPI = $drawAPI;
  }
  public abstract function draw();
}

// create concrete class implementing the Shape interface (abstract class)
class Circle extends Shape {
  private $x;
  private $y;
  private $radius;
  public function __construct($x, $y, $radius, $drawAPI){
    Shape::__construct($drawAPI);
    $this->x = $x;
    $this->y = $y;
    $this->radius = $radius;
  }
  public function draw(){
    $this->drawAPI->drawCircle($this->radius, $this->x, $this->y);
  }
}

// Use Shape and DrawAPI classes to draw different colored circles
// implementation of concrete circles selected at run time.

$redCircle = new Circle(100, 100, 10, new RedCircle);
$greenCircle = new Circle(100, 100, 10, new GreenCircle);
$redCircle->draw();
$greenCircle->draw();

?>
