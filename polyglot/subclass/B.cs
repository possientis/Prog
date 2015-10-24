using System;

public class B : A{
  private int b_;

  public B(int a, int b) : base(a){this.b = b;}
  public B(B rhs) : base(rhs){b = rhs.b;}
  // unlike C++ and Java, C# supports properties
  public int b { get{return b_;} set{b_ = value;}}
  public override void foo(){Console.WriteLine("B::foo() is running");}
  public static void swap(B x, B y){
    A.swap(x,y);
    int temp = x.b; x.b = y.b; y.b = temp;}
}

