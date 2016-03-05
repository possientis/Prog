// the problem of single dispatch polymorphism

interface Person {
  public void pet(Dog d);
  public void pet(Cat c);
}

class Man implements Person {
  public void pet(Dog d){
    System.out.println("Man here, petting dog:" + d.makeSound());
  }
  public void pet(Cat c){
    System.out.println("Man here, petting cat:" + c.makeSound());
  }
}

class Woman implements Person {
  public void pet(Dog d){
    System.out.println("Woman here, petting dog:" + d.makeSound());
  }
  public void pet(Cat c){
    System.out.println("Woman here, petting cat:" + c.makeSound());
  }
}

interface Animal {
  public String makeSound();
}

class Dog implements Animal {
  public String makeSound() {
    return "Wof, wof";
  }
}

class Cat implements Animal {
  public String makeSound() {
    return "Wof, wof";
  }
}

// visitor design pattern allows going round the
// problem of single dispatch polymorphism
// by emulating double dispatch with a mix
// of subtyping (dynamic) polymorphism and
// overloading -> (static) polymorphism
public class Park {
  public static void main(String[] args) {
    Person p = new Man();
    Animal a = new Dog();
    //p.pet(a); // error: no suitable method found for pet(Animal)
  }
}
