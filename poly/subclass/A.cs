using System;

public class A{
  public int a;
  public A(int a){this.a = a;}
  public A(A rhs){a = rhs.a;}
  public virtual void foo(){Console.WriteLine("A::foo() is running");}
}
