public class Main{

  public static void main(String[] args){
    A a = new A(1);
    B b = new B(2,3);
    System.out.println(a.a + ":" + b.a + ":" + b.b);
    a.foo();
    b.foo();

    A c = new B(4,5);
    c.foo();

  }
}
