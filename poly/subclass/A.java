public class A{
  public int a;
  public A(int a){this.a = a;}
  public A(A rhs){a = rhs.a;}
  public void foo(){System.out.println("A::foo() is running");}
  public static void swap(A x, A y){int temp = x.a; x.a = y.a; y.a = temp;}

}
