using System;

class Test{

  public static void Main(){

    A a = new B();
    a.foo();  // B::foo() running
    a.bar();  // A::bar() running oops.


  }
}

class A{

  public virtual void foo(){Console.WriteLine("running A::foo()");}
  public virtual void bar(){Console.WriteLine("running A::bar()");}

}

class B : A{
  public override void foo(){Console.WriteLine("running B::foo()");}
  public new void bar(){Console.WriteLine("running B::foo()");}
}


