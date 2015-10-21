// Main.java
public class Main{

  public static void main(String[] args){
    A a = new A(1);
    B b = new B(2,3);
    System.out.println(a.aGet() + ":" + b.aGet() + ":" + b.bGet());
    a.foo();
    b.foo();
    A c = new B(4,5);
    c.foo();
    A a1 = new A(a);  // copy ctor
    B b1 = new B(b);  // copy ctor
    System.out.println(a1.aGet() + ":" + b1.aGet() + ":" + b1.bGet());

    A a2 = new A(2);
    A.swap(a1,a2);  // rather than C++ A::swap syntax
    System.out.println(a1.aGet() + ":" + a2.aGet());

    B b2 = new B(4,5);
    B.swap(b1,b2);
    System.out.println(b1.aGet() + ":" + b1.bGet() + ":" + b2.aGet() + ":" + b2.bGet());





  }
}
