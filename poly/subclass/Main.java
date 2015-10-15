// Main.java
public class Main{

  public static void main(String[] args){
    A a = new A(1);
    B b = new B(2,3);
    System.out.println(a.a + ":" + b.a + ":" + b.b);
    a.foo();
    b.foo();
    A c = new B(4,5);
    c.foo();
    A a1 = new A(a);  // copy ctor
    B b1 = new B(b);  // copy ctor
    System.out.println(a1.a + ":" + b1.a + ":" + b1.b);

    A a2 = new A(2);
    A.swap(a1,a2);  // rather than C++ A::swap syntax
    System.out.println(a1.a + ":" + a2.a);



  }
}
