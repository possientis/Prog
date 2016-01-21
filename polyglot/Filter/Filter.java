// Filter design pattern
import java.util.*;
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

@FunctionalInterface
interface IPredicate<T>{

  public boolean Test(T t); // single method, everything else 'default' or 'static'

  public static <T> IPredicate<T> isEqual(T targetRef){
    return t -> t.equals(targetRef);
  }

  public default IPredicate<T> not(){
    return t -> !Test(t);
  }
  
  public default IPredicate<T> and(IPredicate<? super T> other){
    return t -> !Test(t) ? false : other.Test(t);
  }
  
  public default IPredicate<T> or(IPredicate<? super T> other){
    return t -> Test(t) ? true : other.Test(t);
  }
}

class Person {

  private final String name;
  private final String gender;
  private final String maritalStatus;

  public Person(String name, String gender, String maritalStatus){
    this.name           = name;
    this.gender         = gender;
    this.maritalStatus  = maritalStatus;
  }

  public String getName()         { return name; }
  public String getGender()       { return gender; }
  public String getMaritalStatus(){ return maritalStatus; }

  @Override
  public boolean equals(Object other){  // possible equality
    if(other instanceof Person){
      return name.equalsIgnoreCase(((Person) other).name);
    } else {
      return false;
    }
  }

  // some static predicates
  public static final IPredicate<Person> male = 
    t -> t.getGender().equalsIgnoreCase("MALE"); 
  public static final IPredicate<Person> female =
    t -> t.getGender().equalsIgnoreCase("FEMALE");
  public static final IPredicate<Person> single =
    t -> t.getMaritalStatus().equalsIgnoreCase("SINGLE"); 
  public static final IPredicate<Person> singleMale =
    single.and(male);
  public static final IPredicate<Person> singleOrFemale =
    single.or(female);

  // sample of known persons
  public static List<Person> people(){
    List<Person> people = new ArrayList<>();
    people.add(new Person("Robert","Male","Single"));
    people.add(new Person("John","Male","Married"));
    people.add(new Person("Laura","Female","Married"));
    people.add(new Person("Diana","Female","Single"));
    people.add(new Person("Mike","Male","Single"));
    people.add(new Person("Bobby","Male","Single"));

    return people;
  }

  // printing list of people
  public static void print(List<Person> people){
    for(Person person : people){
      System.out.print("(" + person.getName() 
          + "," + person.getGender()
          + "," + person.getMaritalStatus()
          + ")\t");
    }
  }

  // The filter method exists on the Stream<T> interface. Don't use this 
  public static List<Person> filter(List<Person> people, IPredicate<Person> p){
    List<Person> newList = new ArrayList<>();
    for(Person person : people){
      if(p.Test(person)) newList.add(person);
    }
    return newList;
  }
}

public class Filter {
  public static void main(String[] args){
    Person john2 = new Person("John","Male","Married");
    List<Person> people = Person.people();
    List<Person> males = Person.filter(people,Person.male);
    List<Person> females = Person.filter(people,Person.female);
    List<Person> singleMales = Person.filter(people, Person.singleMale);
    List<Person> singleOrFemales = Person.filter(people, Person.singleOrFemale);
    IPredicate<Person> notJohn = IPredicate.isEqual(john2).not();
    List<Person> notJohns = Person.filter(people, notJohn);

    System.out.print("Everyone:\t\t"); Person.print(people);
    System.out.print("\nNot John:\t\t"); Person.print(notJohns);
    System.out.print("\nSingle or Female:\t"); Person.print(singleOrFemales);
    System.out.print("\nMales:\t\t\t"); Person.print(males);
    System.out.print("\nSingle Males:\t\t"); Person.print(singleMales);
    System.out.print("\nFemales:\t\t"); Person.print(females);
    System.out.print("\n");
  }
}
