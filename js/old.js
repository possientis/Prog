// Define the class Car
function Car(speed){
  print("Class Car is instantiated");
  this.speed = speed;
}

Car.prototype.speed = 'Car Speed';  // ???
Car.prototype.setSpeed = function(speed){
  this.speed = speed;
  print("Car speed changed");
}

var car1 = new Car(40);
var car2 = new Car(60);

car1.setSpeed(120);
car2.setSpeed(140);

print("Car1 Speed: " + car1.speed);
print("Car2 Speed: " + car2.speed);

function Ferrari(){}
Ferrari.prototype = new Car();
Ferrari.prototype.constructor = Ferrari;
Ferrari.prototype.setSpeed = function(speed){
  this.speed = speed;
  print("Ferrari speed changed");
}

var car = new Ferrari();
car.setSpeed(170);
print("Ferrari car Speed: " + car.speed);


var Man = {gender: 'Male'};
var John = {name:'John Doe', age: 25, __proto__: Man};


print(John.gender);

f = function(x){return 2*x;};

function Person(name,age){
  this.name = name;
  this.age = age;
  this.shoutYourName =function(){
    return 'SHOUTING ' + this.name;
  }
}

var john = new Person('John', 25);
var donn = new Person('Donn', 29);

print(john.__proto__ === Person.prototype);
print(john.__proto__ === Person.prototype);
print(Person.__proto__ === Function.prototype);

Person.prototype.getAllCapsName = function(){
  return this.name.toUpperCase();
};

print(john.getAllCapsName());
print(typeof(Person));
print(Person.__proto__ == Function.prototype);
print(john.__proto__ == Person.prototype);
print(john.__proto__);
print(Person.prototype);
print(Person.prototype.__proto__);
print(Person.prototype.constructor == Person);
print(john.constructor == Person);
print(john.constructor);

print(john.shoutYourName());
print(donn.shoutYourName());

Person.prototype.shhhYourName = function(){
  return 'shhh ' + this.name;
};

print(john.shhhYourName());
print(donn.shhhYourName());

// changing definition of john only
john.shoutYourName = function(){
  return 'SHOUTING ' + this.name + '!!!!!!';
};

// changing definition in prototype
Person.prototype.shhhYourName = function(){
  return 'shhh ' + this.name + '!!!!!!';
};


print(john.shoutYourName());
print(donn.shoutYourName());

print(john.shhhYourName());
print(donn.shhhYourName());


