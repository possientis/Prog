// Bridge design patter

// bridge implementation interface
function DrawAPI(){
};


DrawAPI.prototype.drawCircle = function(radius, x, y){
  print("DrawAPI::drawCircle is not implemented");
}


// concrete bridge implementation classes implementing DrawAPI interface
function RedCircle(){
};
this.__proto__ = RedCircle.prototype; // redundant.
RedCircle.prototype.__proto__ = new DrawAPI();
RedCircle.prototype.drawCircle = function(radius, x, y){
  print("Drawing Circle[ color: red  , radius: "+radius+", x: "+x+", y: "+y+"]");
};

function GreenCircle(){
};
GreenCircle.prototype.__proto__ = new DrawAPI();
GreenCircle.prototype.drawCircle = function(radius, x, y){
  print("Drawing Circle[ color: green, radius: "+radius+", x: "+x+", y: "+y+"]");
};


// create an abstract class Shape using the DrawAPI interface.
function Shape(drawAPI){
  this.drawAPI = drawAPI;
};

Shape.prototype.draw = function(){  // abstraction need not follow imp API
  print("Shape::draw is not implemented");
};

// create concrete class implementing the Shape interface (abstract class)
function Circle(x, y, radius, drawAPI){
};

redCircle = new RedCircle();
redCircle.drawCircle(10,100,100);
drawAPI = redCircle.__proto__;
drawAPI.drawCircle(10,100,100);

function f(x){print(x == undefined);};
print(Object.prototype.__proto__ == null);
print(typeof(Object.prototype))
