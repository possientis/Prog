using System;

public class A{
  private int a_;


  public A(int a){this.a = a;}
  public A(A rhs){a = rhs.a;}
  // unlike C++ and Java, C# supports properties
  public int a { get{return a_;} set{a_ = value;}}
  public virtual void foo(){Console.WriteLine("A::foo() is running");}
  public static void swap(A x, A y){int temp = x.a; x.a = y.a; y.a =temp;}
}
