<?php
// Factory design pattern
interface Shape {
  public function draw();
}

class Rectangle implements Shape {
  public function draw(){
    echo 'Inside Rectangle::draw() method.'.PHP_EOL;
  }
}

class Square implements Shape {
  public function draw(){
    echo 'Inside Square::draw() method.'.PHP_EOL;
  }
}

class Circle implements Shape {
  public function draw(){
    echo 'Inside Circle::draw() method.'.PHP_EOL;
  }
}

class ShapeFactory {
  // use getShape method to get object of type Shape
  public function getShape($shapeType){
    if(empty($shapeType)) return NULL;

    if(strtoupper($shapeType) == "CIRCLE"){
      return new Circle;
    } else if(strtoupper($shapeType) == "RECTANGLE"){
      return new Rectangle;
    } else if(strtoupper($shapeType) == "SQUARE"){
      return new Square;
    }
    return NULL;
  }
}

$shapeFactory = new ShapeFactory;
// get an object of type Circle and call its draw method.
$shape1 = $shapeFactory->getShape("CIRCLE");
$shape1->draw();

// get an object of type Rectangle and call its draw method.
$shape2 = $shapeFactory->getShape("RECTANGLE");
$shape2->draw();

// get an object of type Square and call its draw method.
$shape3 = $shapeFactory->getShape("SQUARE");
$shape3->draw();

?>
