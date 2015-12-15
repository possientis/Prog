print(Number.MAX_VALUE);
print(Number.MIN_VALUE);
var str = "Here are some escaped characters \"";
print(str);
print(str.substring(5,10));

function Animal(breed){
  this.breed = breed;
  this.bar = function(){
    print("Animal::bar is running");
  }
}

Animal.prototype.foo = function(){
  print("Animal::foo is running");
}

var dog = new Animal("abc");

dog.name = "doggy";

print(dog.name);
dog.foo();
dog.bar();
print(dog.breed);


