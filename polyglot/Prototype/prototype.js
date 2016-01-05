// Prototype design pattern
// Imagine that in order to instantiate certain objects we need to carry out
// expensive database queries. In order to improve performance, it would 
// be beneficial to cache whatever object is created from the database
// and return a copy of the cached object whenever a subsequent request
// for object instantiation arises.

function Shape(){
}
Shape.prototype.draw = function(){
  print("Shape::draw is not implemented");
}
Shape.prototype.getId = function(){
  return this.id;
}
Shape.prototype.setId = function(id){
  this.id = id;
}
Shape.prototype.clone = function(){
  print("Shape::clone is not implemented");
}

function Rectangle(){
  Shape.call(this);
}
Rectangle.prototype = Object.create(Shape.prototype);
Rectangle.prototype.draw = function(){
  print("Inside Rectangle::draw() method.");
}
Rectangle.prototype.clone = function(){
  clone = new Rectangle();
  clone.setId(this.id);
  return clone;
}

function Square(){
  Shape.call(this);
}
Square.prototype = Object.create(Shape.prototype);
Square.prototype.draw = function(){
  print("Inside Square::draw() method.");
}
Square.prototype.clone = function(){
  clone = new Square();
  clone.setId(this.id);
  return clone;
}

function Circle(){
  Shape.call(this);
}
Circle.prototype = Object.create(Shape.prototype);
Circle.prototype.draw = function(){
  print("Inside Circle::draw() method.");
}
Circle.prototype.clone = function(){
  clone = new Circle();
  clone.setId(this.id);
  return clone;
}

function PrototypeManager(){
  this.shapeMap = {}
}
PrototypeManager.prototype.loadCache = function(){
  rect = new Rectangle();
  rect.setId("1");
  this.shapeMap[rect.getId()] = rect;

  square = new Square();
  square.setId("2");
  this.shapeMap[square.getId()] = square;

  circle = new Circle();
  circle.setId("3");
  this.shapeMap[circle.getId()] = circle;
}
PrototypeManager.prototype.getShape= function(shapeId){
  cachedShape = this.shapeMap[shapeId];
  return cachedShape.clone();
}

// need a prototype manager
manager = new PrototypeManager();
// prototype manager registers a few prototypes
manager.loadCache();
// prototype manager can now be used as factory object
clonedShape1 = manager.getShape("1");
clonedShape1.draw();

clonedShape2 = manager.getShape("2");
clonedShape2.draw();

clonedShape3 = manager.getShape("3");
clonedShape3.draw();


