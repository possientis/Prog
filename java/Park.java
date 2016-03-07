// the problem of single dispatch polymorphism

interface Person {
  public void pet(Dog d);
  public void pet(Cat c);
  public void accept(Animal a);
}

class Man implements Person {
  public void pet(Dog d){
    System.out.println("Man here, petting dog: " + d.makeSound());
  }
  public void pet(Cat c){
    System.out.println("Man here, petting cat: " + c.makeSound());
  }

  public void accept(Animal a){
    System.out.println("Man here, petting " + a.species() + ": " + a.makeSound());
  }
}

class Woman implements Person {
  public void pet(Dog d){
    System.out.println("Woman here, petting dog: " + d.makeSound());
  }
  public void pet(Cat c){
    System.out.println("Woman here, petting cat: " + c.makeSound());
  }

  public void accept(Animal a){
    System.out.println("Woman here, petting " + a.species() + ": " + a.makeSound());
  }
}

interface Animal {
  public String makeSound();
  public String species();
}

class Dog implements Animal {
  public String makeSound() {
    return "Wof, wof";
  }
  public String species() {
    return "dog";
  }
}

class Cat implements Animal {
  public String makeSound() {
    return "Miaw, miaw";
  }

  public String species(){
    return "cat";
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
    Person q = new Woman();
    Animal a = new Dog();
    Animal b = new Cat();

    p.accept(a);
    p.accept(b);
    q.accept(a);
    q.accept(b);


    //p.pet(a); // error: no suitable method found for pet(Animal)
  }
}
