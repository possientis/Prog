using System;

public class B : A{
  public int b;
  public B(int a, int b) : base(a){this.b = b;}
  public B(B rhs) : base(rhs){b = rhs.b;}
  public override void foo(){Console.WriteLine("B::foo() is running");}
}

