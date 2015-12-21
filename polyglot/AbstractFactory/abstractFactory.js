// Abstract Factory design pattern
// the Abstract Factory pattern looks like the factory pattern 
// applied to the production of various factories

function Shape(){
};
Shape.prototype.draw = function(){
  print("Shape::draw is not implemented");
};

function AbstractShape(){
  Shape.call(this);
};
AbstractShape.COLOR = Object.freeze({RED:1, GREEN:2, BLUE:3});
AbstractShape.asString = function(color){
  switch(color){
    case AbstractShape.COLOR.RED:
      return "red";
    case AbstractShape.COLOR.GREEN:
      return "green";
    case AbstractShape.COLOR.BLUE:
      return "blue";
    default:
      return "unknown color";
  }
};
AbstractShape.prototype = Object.create(Shape.prototype);
AbstractShape.prototype.draw = function(){
  print("AbstractShape::draw is not implemented");
};

function Rectangle(color){
  AbstractShape.call(this);
  this._color = color;
};
Rectangle.prototype = Object.create(AbstractShape.prototype);
Rectangle.prototype.draw = function(){
  print("Drawing " + AbstractShape.asString(this._color) + " rectangle");
}

function Square(color){
  AbstractShape.call(this);
  this._color = color;
};
Square.prototype = Object.create(AbstractShape.prototype);
Square.prototype.draw = function(){
  print("Drawing " + AbstractShape.asString(this._color) + " square");
}

function Circle(color){
  AbstractShape.call(this);
  this._color = color;
};
Circle.prototype = Object.create(AbstractShape.prototype);
Circle.prototype.draw = function(){
  print("Drawing " + AbstractShape.asString(this._color) + " circle");
}


// using the template method pattern here, as the actual
// behaviour of 'getShape' will be defined via specialization
// of virtual method getColor through subclassing

function AbstractShapeFactory(){
};
AbstractShapeFactory.prototype.getColor = function(){
  print("AbstractShapeFactory::getColor is not implemented");
};
AbstractShapeFactory.prototype.getShape = function(shapeType){
  if(shapeType.toUpperCase() === "CIRCLE"){
    return new Circle(this.getColor());
  } else if(shapeType.toUpperCase() === "RECTANGLE"){
    return new Rectangle(this.getColor());
  } else if(shapeType.toUpperCase() === "SQUARE"){
    return new Square(this.getColor());
  } else return null;
};

// However the benefit of subclassing over maintaining
// 'mColor' state in base class is not that clear in this simple case
// It is propably beneficial when the distinction between various
// families of widgets (IShape) goes well beyond color difference.

function RedShapeFactory(){
  AbstractShapeFactory.call(this);
};
RedShapeFactory.prototype = Object.create(AbstractShapeFactory.prototype);
RedShapeFactory.prototype.getColor = function(){
  return AbstractShape.COLOR.RED;
};

function GreenShapeFactory(){
  AbstractShapeFactory.call(this);
};
GreenShapeFactory.prototype = Object.create(AbstractShapeFactory.prototype);
GreenShapeFactory.prototype.getColor = function(){
  return AbstractShape.COLOR.GREEN;
};

function BlueShapeFactory(){
  AbstractShapeFactory.call(this);
};
BlueShapeFactory.prototype = Object.create(AbstractShapeFactory.prototype);
BlueShapeFactory.prototype.getColor = function(){
  return AbstractShape.COLOR.BLUE;
};

// Factory of factories. The Abstract Factory design pattern is a case
// of Factory design pattern applied to various factory types.

function FactoryProducer(){
};
FactoryProducer.prototype.getFactory = function(factoryType){
  if(factoryType.toUpperCase() === "RED"){
    return new RedShapeFactory();
  } else if(factoryType.toUpperCase() === "GREEN"){
    return new GreenShapeFactory();
  } else if(factoryType.toUpperCase() === "BLUE"){
    return new BlueShapeFactory();
  } else return null;
};

producer = new FactoryProducer();

// producing set of red widgets
redFactory = producer.getFactory("Red");
shape1 = redFactory.getShape("CIRCLE");
shape2 = redFactory.getShape("RECTANGLE");
shape3 = redFactory.getShape("SQUARE");
shape1.draw();
shape2.draw();
shape3.draw();

// producing set of green widgets
greenFactory = producer.getFactory("Green");
shape1 = greenFactory.getShape("CIRCLE");
shape2 = greenFactory.getShape("RECTANGLE");
shape3 = greenFactory.getShape("SQUARE");
shape1.draw();
shape2.draw();
shape3.draw();


// producing set of blue widgets
blueFactory = producer.getFactory("Blue");
shape1 = blueFactory.getShape("CIRCLE");
shape2 = blueFactory.getShape("RECTANGLE");
shape3 = blueFactory.getShape("SQUARE");
shape1.draw();
shape2.draw();
shape3.draw();






