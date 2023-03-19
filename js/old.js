// Define the class Car
function Car(speed){
  console.log("Class Car is instantiated");
  this.speed = speed;
}

Car.prototype.speed = 'Car Speed';  // ???
Car.prototype.setSpeed = function(speed){
  this.speed = speed;
  console.log("Car speed changed");
}

var car1 = new Car(40);
var car2 = new Car(60);

car1.setSpeed(120);
car2.setSpeed(140);

console.log("Car1 Speed: " + car1.speed);
console.log("Car2 Speed: " + car2.speed);

function Ferrari(){}
Ferrari.prototype = new Car();
Ferrari.prototype.constructor = Ferrari;
Ferrari.prototype.setSpeed = function(speed){
  this.speed = speed;
  console.log("Ferrari speed changed");
}

var car = new Ferrari();
car.setSpeed(170);
console.log("Ferrari car Speed: " + car.speed);


var Man = {gender: 'Male'};
var John = {name:'John Doe', age: 25, __proto__: Man};


console.log(John.gender);

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

console.log(john.__proto__ === Person.prototype);
console.log(john.__proto__ === Person.prototype);
console.log(Person.__proto__ === Function.prototype);

Person.prototype.getAllCapsName = function(){
  return this.name.toUpperCase();
};

console.log(john.getAllCapsName());
console.log(typeof(Person));
console.log(Person.__proto__ == Function.prototype);
console.log(john.__proto__ == Person.prototype);
console.log(john.__proto__);
console.log(Person.prototype);
console.log(Person.prototype.__proto__);
console.log(Person.prototype.constructor == Person);
console.log(john.constructor == Person);
console.log(john.constructor);

console.log(john.shoutYourName());
console.log(donn.shoutYourName());

Person.prototype.shhhYourName = function(){
  return 'shhh ' + this.name;
};

console.log(john.shhhYourName());
console.log(donn.shhhYourName());

// changing definition of john only
john.shoutYourName = function(){
  return 'SHOUTING ' + this.name + '!!!!!!';
};

// changing definition in prototype
Person.prototype.shhhYourName = function(){
  return 'shhh ' + this.name + '!!!!!!';
};


console.log(john.shoutYourName());
console.log(donn.shoutYourName());

console.log(john.shhhYourName());
console.log(donn.shhhYourName());


