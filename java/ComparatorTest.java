import java.util.*;

public class ComparatorTest {
  public static void main(String[] args) {
    List<Person> personList = Person.createShortList();
    // Sort with Inner Class
    Collections.sort(personList, new Comparator<Person>(){
      public int compare(Person p1, Person p2){
        return p1.getFirstName().compareTo(p2.getFirstName());
      }
    });
    System.out.println("=== Sorted Asc FirstName ===");
    for(Person p:personList){
      p.printName();
    }
    // Use Lambda instead
    // Print Asc
    System.out.println("=== Sorted Asc FirstName ===");
    Collections.sort(personList, (Person p1, Person p2) -> p1.getFirstName().compareTo(p2.getFirstName()));
    for(Person p:personList){
      p.printName();
    }
    // Print Desc
    System.out.println("=== Sorted Desc FirstName ===");
    Collections.sort(personList, (p1,  p2) -> p2.getFirstName().compareTo(p1.getFirstName()));
    for(Person p:personList){
      p.printName();
    }
  }
}


class Person{
  private final String firstName;
  public static List<Person> createShortList(){
    List<Person> list = new ArrayList<>();
    list.add(new Person("John"));
    list.add(new Person("Paul"));
    list.add(new Person("Luc"));
    list.add(new Person("Matthew"));
    list.add(new Person("George"));
    list.add(new Person("Robert"));
    list.add(new Person("Eva"));
    list.add(new Person("Adam"));
    return list;
  }
  public Person(String firstName){this.firstName = firstName;}
  public String getFirstName(){return firstName;}
  public void printName(){
    System.out.println(firstName);
  }
}
  
