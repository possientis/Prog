// Bridge design pattern

// bridge implementation interface
function DrawAPI(){
};
DrawAPI.prototype.drawCircle = function(radius, x, y){
  print("DrawAPI::drawCircle is not implemented");
}

// concrete bridge implementation classes implementing DrawAPI interface
function RedCircle(){
  DrawAPI.call(this);                     // not useful as DrawAPI has no data
};
RedCircle.prototype =  Object.create(DrawAPI.prototype);
RedCircle.prototype.drawCircle = function(radius, x, y){
  print("Drawing Circle[ color: red  , radius: "+radius+", x: "+x+", y: "+y+"]");
};

function GreenCircle(){
  DrawAPI.call(this);                      // not useful as DrawAPI has no data
};
GreenCircle.prototype =  Object.create(DrawAPI.prototype);
GreenCircle.prototype.drawCircle = function(radius, x, y){
  print("Drawing Circle[ color: green, radius: "+radius+", x: "+x+", y: "+y+"]");
};

// create an abstract class Shape using the DrawAPI interface.
function Shape(drawAPI){
  this.drawAPI = drawAPI;
};
Shape.prototype.draw = function(){
  print("Shape::draw is not implemented");
};

// create concrete class implementing the Shape interface (abstract class)
function Circle(x, y, radius, drawAPI){
  Shape.call(this, drawAPI);
  this.x = x;
  this.y = y;
  this.radius = radius;
};
Circle.prototype = Object.create(Shape.prototype);
Circle.prototype.draw = function(){
  this.drawAPI.drawCircle(this.radius,this.x,this.y);
};

// Use Shape and DrawAPI classes to draw different colored circles
// implementation of concrete circles selected at run time.
redCircle = new Circle(100, 100, 10,new RedCircle());
greenCircle = new Circle(100, 100, 10, new GreenCircle());
redCircle.draw();
greenCircle.draw();



