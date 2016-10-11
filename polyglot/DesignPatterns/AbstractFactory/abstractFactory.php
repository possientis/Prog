<?php
// Abstract Factory design pattern
// the Abstract Factory pattern looks like the factory pattern 
// applied to the production of various factories

interface Shape {
  public function draw();
}

abstract class COLOR {
  const RED = 0;
  const GREEN = 1;
  const BLUE = 2;
}

abstract class AbstractShape implements Shape {

  protected static final function asString($color){
    switch($color){
    case COLOR::RED:
      return "red";
    case COLOR::GREEN:
      return "green";
    case COLOR::BLUE:
      return "blue";
    default:
      return "unknown color";
    }
  }

  protected $color;
}

class Rectangle extends AbstractShape {
  public function __construct($color){
    $this->color = $color;
  }
  public function draw(){
    echo 'Drawing '.self::asString($this->color).' rectangle'.PHP_EOL;
  }
}

class Square extends AbstractShape {
  public function __construct($color){
    $this->color = $color;
  }
  public function draw(){
    echo 'Drawing '.self::asString($this->color).' square'.PHP_EOL;
  }
}

class Circle extends AbstractShape {
  public function __construct($color){
    $this->color = $color;
  }
  public function draw(){
    echo 'Drawing '.self::asString($this->color).' circle'.PHP_EOL;
  }
}

// using the template method pattern here, as the actual
// behaviour of 'getShape' will be defined via specialization
// of virtual method getColor through subclassing
abstract class AbstractShapeFactory {
  abstract public function getColor();

  public function getShape($shapeType){
    if(empty($shapeType)) return NULL;

    if(strtoupper($shapeType) == "CIRCLE"){
      return new Circle($this->getColor());
    } else if(strtoupper($shapeType) == "RECTANGLE"){
      return new Rectangle($this->getColor());
    } else if(strtoupper($shapeType) == "SQUARE"){
      return new Square($this->getColor());
    }

    return NULL;
  }
}

// However the benefit of subclassing over maintaining
// '$color' state in base class is not that clear in this simple case
// It is propably beneficial when the distinction between various
// families of widgets (Shape) goes well beyond color difference.
class RedShapeFactory extends AbstractShapeFactory {
  public function getColor(){return COLOR::RED;}
}

class GreenShapeFactory extends AbstractShapeFactory {
  public function getColor(){return COLOR::GREEN;}
}

class BlueShapeFactory extends AbstractShapeFactory {
  public function getColor(){return COLOR::BLUE;}
}

// Factory of factories. The Abstract Factory design pattern is a case
// of Factory design pattern applied to various factory types.
class FactoryProducer {
  public function getFactory($factoryType){
    if(empty($factoryType)) return NULL;

    if(strtoupper($factoryType) == "RED"){
      return new RedShapeFactory;
    } else if(strtoupper($factoryType) == "GREEN"){
      return new GreenShapeFactory;
    } else if (strtoupper($factoryType) == "BLUE"){
      return new BlueShapeFactory;
    }

    return NULL;
  }
}

$producer = new FactoryProducer;
// producing set of red widgets
$redFactory = $producer->getFactory("Red");
$shape1 = $redFactory->getShape("CIRCLE");
$shape2 = $redFactory->getShape("RECTANGLE");
$shape3 = $redFactory->getShape("SQUARE");
$shape1->draw();
$shape2->draw();
$shape3->draw();

// producing set of green widgets
$greenFactory = $producer->getFactory("Green");
$shape4 = $greenFactory->getShape("CIRCLE");
$shape5 = $greenFactory->getShape("RECTANGLE");
$shape6 = $greenFactory->getShape("SQUARE");
$shape4->draw();
$shape5->draw();
$shape6->draw();

// producing set of blue widgets
$blueFactory = $producer->getFactory("Blue");
$shape7 = $blueFactory->getShape("CIRCLE");
$shape8 = $blueFactory->getShape("RECTANGLE");
$shape9 = $blueFactory->getShape("SQUARE");
$shape7->draw();
$shape8->draw();
$shape9->draw();






?>
