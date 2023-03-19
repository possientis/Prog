console.log(Number.MAX_VALUE);
console.log(Number.MIN_VALUE);
var str = "Here are some escaped characters \"";
console.log(str);
console.log(str.substring(5,10));

function Animal(breed){
  this.breed = breed;
  this.bar = function(){
    console.log("Animal::bar is running");
  }
}

Animal.prototype.foo = function(){
  console.log("Animal::foo is running");
}

var dog = new Animal("abc");

dog.name = "doggy";

console.log(dog.name);
dog.foo();
dog.bar();
console.log(dog.breed);


