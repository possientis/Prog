// Filter design pattern

// This pattern allows to use a list of objects and perform
// a filtering operation on that list so as to obtain a new
// list comprised of those objects in the initial list which
// satisfy a given predicate. Since the introduction of
// lambda expressions within Java 8 and the introduction
// of functional interfaces such as Predicate<T>, this 
// pattern is not very useful in practice and amounts 
// mainly to a coding exercise aiming at re-implementing
// the Predicate<T> java interface. This pattern is not
// useful either in functional languages which directly 
// support first class functions and filter operations on lists.

function Predicate(predicate){
  this.predicate = predicate;
}
Predicate.prototype.test = function(t){
  return this.predicate(t);
}
// static member
Predicate.isEqual = function(targetRef){
  return new Predicate(function(t){ return t.equals(targetRef); });
}
Predicate.prototype.not = function(){
  // defining lambda  in two steps to avoid referring to 'this' 
  // inside body of anonymous function, which is used to define
  // 'this', leading to infinite recursion. Similar issue in C++
  var func = this.predicate;
  return new Predicate(function(t){ return !func(t); });
}

Predicate.prototype.and = function(other){
  var func = this.predicate;
  return new Predicate(function(t){ return !func(t) ? false : other.test(t); });
}

Predicate.prototype.or = function(other){
  var func = this.predicate;
  return new Predicate(function(t){ return func(t) ? true : other.test(t); });
}

function Person(name, gender, maritalStatus){
  this.name           = name;
  this.gender         = gender;
  this.maritalStatus  = maritalStatus;
}
Person.prototype.getName          = function(){ return this.name; }
Person.prototype.getGender        = function(){ return this.gender; }
Person.prototype.getMaritalStatus = function(){ return this.maritalStatus; }
// plausible definition of equality
Person.prototype.equals = function(other){
  if(other instanceof Person){
    return this.getName().toUpperCase() === other.getName().toUpperCase();
  } else {
    return false;
  }
}

// some static predicates
Person.male = new Predicate(function(t){
  return t.getGender().toUpperCase() === "MALE";
});

Person.female = new Predicate(function(t){
  return t.getGender().toUpperCase() === "FEMALE";
});

Person.single = new Predicate(function(t){
  return t.getMaritalStatus().toUpperCase() === "SINGLE";
});

Person.singleMale = Person.single.and(Person.male);
Person.singleOrFemale = Person.single.or(Person.female);

Person.people = function(){
  var list = new Array();
  list[0] = new Person("Robert","Male","Single");
  list[1] = new Person("John","Male","Married");
  list[2] = new Person("Laura","Female","Married");
  list[3] = new Person("Diana","Female","Single");
  list[4] = new Person("Mike","Male","Single");
  list[5] = new Person("Bobby","Male","Single");
  return list;
}

// does not actually print, simply returns output string
// rhino javascript seems to provide no way of writing 
// to standard output without an end-of-line character
Person.print = function(list){
  var outString = "";
  for(i = 0; i < list.length; ++i){
    var person = list[i];
    outString += "(" + person.getName()
      + "," + person.getGender()
      + "," + person.getMaritalStatus()
      + ")\t";
  }
  return outString;
}

// Javascript supports a filter operation on arrays ...
Person.filter = function(list,predicate){
  return list.filter(function(t){
    return predicate.test(t);
  });
}

var john2 = new Person("John","Male","Married");
var notJohn = Predicate.isEqual(john2).not();

people          = Person.people();
males           = Person.filter(people, Person.male);
females         = Person.filter(people, Person.female);
singleMales     = Person.filter(people, Person.singleMale);
singleOrFemales = Person.filter(people, Person.singleOrFemale);
notJohns        = Person.filter(people, notJohn);

print("Everyone:\t\t"       + Person.print(people));
print("Not John:\t\t"       + Person.print(notJohns));
print("Single or Female:\t" + Person.print(singleOrFemales));
print("Males:\t\t\t"        + Person.print(males));
print("Single Males:\t\t"   + Person.print(singleMales));
print("Females:\t\t"        + Person.print(females));



