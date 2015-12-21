// Factory design pattern
function Shape() {
};
Shape.prototype.draw = function(){
  print("Shape::draw is not implemented");
}

function Rectangle(){
  Shape.call(this); // not useful as Shape has no data
};
Rectangle.prototype = Object.create(Shape.prototype);
Rectangle.prototype.draw = function(){
  print("Inside Rectangle::draw() method.");
};

function Square(){
  Shape.call(this); // not useful as Shape has no data
};
Square.prototype = Object.create(Shape.prototype);
Square.prototype.draw = function(){
  print("Inside Square::draw() method.");
};

function Circle(){
  Shape.call(this); // not useful as Shape has no data
};
Circle.prototype = Object.create(Shape.prototype);
Circle.prototype.draw = function(){
  print("Inside Circle::draw() method.");
};

function ShapeFactory(){
};
ShapeFactory.prototype.getShape = function(shapeType){
  if(shapeType === "") return null;
  if(shapeType.toUpperCase() === "CIRCLE"){
    return new Circle();
  } else if(shapeType.toUpperCase() === "RECTANGLE"){
    return new Rectangle();
  } else if(shapeType.toUpperCase() === "SQUARE"){
    return new Square();
  } else {
    return null;
  }
}

shapeFactory = new ShapeFactory();

// get an object of type Circle and call its draw method
shape1 = shapeFactory.getShape("CIRCLE");
shape1.draw();

// get an object of type Rectangle and call its draw method
shape2 = shapeFactory.getShape("RECTANGLE");
shape2.draw();

// get an object of type Square and call its draw method
shape3 = shapeFactory.getShape("SQUARE");
shape3.draw();





