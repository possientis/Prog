// Filter design pattern
using System;
using System.Collections.Generic;
using System.Linq;  // Where method

using PersonList = System.Collections.Generic.IEnumerable<Person>;

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
// support first class functions and filter operations on
// lists, or in C# which supports Where on IEnumerable

public delegate bool PredicateFunc<T>(T t);

class Predicate<T> {
  private readonly PredicateFunc<T> test;
  public Predicate(PredicateFunc<T> test){ this.test = test; }
  public bool Test(T t){ return test(t); }

  public static Predicate<T> IsEqual(T targetRef){
    return new Predicate<T>(t => t.Equals(targetRef));
  }

  public Predicate<T> Not(){
    return new Predicate<T>(t => !Test(t));
  }

  public Predicate<T> And(Predicate<T> other){
    return new Predicate<T>(t => !Test(t) ? false : other.Test(t));
  }

  public Predicate<T> Or(Predicate<T> other){
    return new Predicate<T>(t => Test(t) ? true : other.Test(t));
  }
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

  // check list of 'Equals' overriding:
  // 1. having the right signature: bool Equals(object other)
  // 2. accompanying override for GetHashCode: 
  // x == y => x.GetHashCode == y.GetHashCode
  // 3. It is not defined in terms of mutable fields
  // 4. It defines an equivalence relation
  public override bool Equals(object other){  // possibly equality
    if(other is Person){
      return Name.Equals(((Person) other).Name);
    } else {
      return false;
    }
  }
  // it is a sin to override 'Equals' without overriding 'GetHashCode'
  public override int GetHashCode(){
    return Name.ToUpper().GetHashCode();
  }


  public static readonly Predicate<Person> male =
    new Predicate<Person>(
        t => t.Gender.Equals("MALE",StringComparison.OrdinalIgnoreCase)
    );

  public static readonly Predicate<Person> female =
    new Predicate<Person>(
        t => t.Gender.Equals("FEMALE",StringComparison.OrdinalIgnoreCase)
    );

  public static readonly Predicate<Person> single =
    new Predicate<Person>(
        t => t.MaritalStatus.Equals("SINGLE",StringComparison.OrdinalIgnoreCase)
    );

  public static readonly Predicate<Person> singleMale = single.And(male);
  public static readonly Predicate<Person> singleOrFemale = single.Or(female);


  public static PersonList People(){
    IList<Person> people = new List<Person>();
    people.Add(new Person("Robert","Male","Single"));
    people.Add(new Person("John","Male","Married"));
    people.Add(new Person("Laura","Female","Married"));
    people.Add(new Person("Diana","Female","Single"));
    people.Add(new Person("Mike","Male","Single"));
    people.Add(new Person("Bobby","Male","Single"));

    return people as PersonList;  // explicit upcast
  }

  public static void Print(PersonList list){
    foreach(Person person in list){
      Console.Write("(" + person.Name
          + "," + person.Gender
          + "," + person.MaritalStatus
          + ")\t");
    }
  }

  public static PersonList filter(PersonList list, Predicate<Person> pred){
    return list.Where(p => pred.Test(p));
  }
}

public class Filter {
  public static void Main(string[] args){
    Person john2 = new Person("John","Male","Married");
    Predicate<Person> notJohn = Predicate<Person>.IsEqual(john2).Not();

    PersonList people          = Person.People();
    PersonList males           = Person.filter(people, Person.male);
    PersonList females         = Person.filter(people, Person.female);
    PersonList singleMales     = Person.filter(people, Person.singleMale);
    PersonList singleOrFemales = Person.filter(people, Person.singleOrFemale);
    PersonList notJohns        = Person.filter(people, notJohn);

    Console.Write("Everyone:\t\t");         Person.Print(people);    
    Console.Write("\nNot John:\t\t");       Person.Print(notJohns);    
    Console.Write("\nSingle or Female:\t"); Person.Print(singleOrFemales);    
    Console.Write("\nMales:\t\t\t");        Person.Print(males);    
    Console.Write("\nSingle Males:\t\t");   Person.Print(singleMales);    
    Console.Write("\nFemales:\t\t");        Person.Print(females);    
    Console.Write("\n");
  }
}
