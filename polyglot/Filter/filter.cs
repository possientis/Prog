// Filter design pattern
using System;
using System.Collections.Generic;
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

interface IPredicate<T>{
  bool Test(T t);
}

class Person {

  private readonly string name;
  private readonly string gender;
  private readonly string maritalStatus;

  public Person(string name, string gender, string maritalStatus){
    this.name = name;
    this.gender = gender;
    this.maritalStatus = maritalStatus;
  }

  public string Name            {get{return name;}}
  public string Gender          {get{return gender;}}
  public string MaritalStatus   {get{return maritalStatus;}}

  // simply to avoid warning on overriding Equals
  public override int GetHashCode(){
    return Name.GetHashCode();
  }

  public override bool Equals(object other){  // possibly equality
    if(other is Person){
      return Name.Equals(((Person) other).Name);
    } else {
      return false;
    }
  }

  public static IList<Person> People(){
    IList<Person> people = new List<Person>();
    people.Add(new Person("Robert","Male","Single"));
    people.Add(new Person("John","Male","Married"));
    people.Add(new Person("Laura","Female","Married"));
    people.Add(new Person("Diana","Female","Single"));
    people.Add(new Person("Mike","Male","Single"));
    people.Add(new Person("Bobby","Male","Single"));

    return people;
  }

  public static void Print(IList<Person> list){
    foreach(Person person in list){
      Console.Write("(" + person.Name
          + "," + person.Gender
          + "," + person.MaritalStatus
          + ")\t");
    }
  }

  public static IList<Person> filter(IList<Person> list, IPredicate<Person> pred){
    /*
    IList<Person> newList = new List<Person>();
    foreach(Person person in list){
      if(pred.Test(person)) newList.Add(person);
    }
    return newList;
    */
    return list;
  }

}

public class Filter {
  public static void Main(string[] args){
//    Person john2 = new Person("John","Male","Married");

    IList<Person> people            = Person.People();
    IList<Person> males             = Person.filter(people, null);
    IList<Person> females           = Person.filter(people, null);
    IList<Person> singleMales       = Person.filter(people, null);
    IList<Person> singleOrFemales   = Person.filter(people, null);
    IList<Person> notJohns          = Person.filter(people, null);

    Console.Write("Everyone:\t\t");         Person.Print(people);    
    Console.Write("\nNot John:\t\t");       Person.Print(notJohns);    
    Console.Write("\nSingle or Female:\t"); Person.Print(singleOrFemales);    
    Console.Write("\nMales:\t\t\t");        Person.Print(males);    
    Console.Write("\nSingle Males:\t\t");   Person.Print(singleMales);    
    Console.Write("\nFemales:\t\t");        Person.Print(females);    
    Console.Write("\n");
  }
}
