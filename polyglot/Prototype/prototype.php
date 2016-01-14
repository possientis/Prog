<?php
// Prototype design pattern
// Imagine that in order to instantiate certain objects we need to carry out
// expensive database queries. In order to improve performance, it would 
// be beneficial to cache whatever object is created from the database
// and return a copy of the cached object whenever a subsequent request
// for object instantiation arises.

abstract class Shape {

  private $id;
  abstract public function draw();

  public function getId(){
    return $this->id;
  }

  public function setId($id){
    $this->id = $id;
  }
}

class Rectangle extends Shape {
  public function draw(){
    echo "Inside Rectangle::draw() method.\n";
  }

  // This is not an override, as default cloning always occurs
  // This method is meant to refine the cloning process if 
  // needed. In this case, simple default shallow copy is fine
  public function __clone() {
    // no need to do anything beyond default
  }
}

class Square extends Shape {
  public function draw(){
    echo "Inside Square::draw() method.\n";
  }

  public function __clone() {
    // no need to do anything beyond default
  }
}

class Circle extends Shape {
  public function draw(){
    echo "Inside Circle::draw() method.\n";
  }

  public function __clone() {
    // no need to do anything beyond default
  }
}


class PrototypeManager {
  public function __construct(){
    $this->shapeMap = [];
  }

  public function getShape($shapeId){
    $cachedShape = $this->shapeMap[$shapeId];
    return clone $cachedShape;
  }

  public function loadCache(){
    $rect = new Rectangle;
    $rect->setId("1");
    $this->shapeMap["1"] = $rect;

    $square = new Square;
    $square->setId("2");
    $this->shapeMap["2"] = $square;

    $circle = new Circle;
    $circle->setId("3");
    $this->shapeMap["3"] = $circle;
  }
}


// need a prototype manager
$manager = new PrototypeManager;
// prototype manager registers a few prototypes
$manager->loadCache();
// prototype manager can now be used as factory object
$clonedShape1 = $manager->getShape("1");
$clonedShape1->draw();

$clonedShape2 = $manager->getShape("2");
$clonedShape2->draw();

$clonedShape3 = $manager->getShape("3");
$clonedShape3->draw();


