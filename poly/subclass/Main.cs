// Main.cs
using System;

static class Program{
  static void Main (string[] args)
  {
    A a = new A(1);
    B b = new B(2,3);
    Console.WriteLine(a.a + ":" + b.a + ":" + b.b);
    a.foo();
    b.foo();
    A c = new B(4,5);
    c.foo();

    A a1 = new A(a);  // copy ctor
    B b1 = new B(b);  // copy ctor
    Console.WriteLine(a1.a + ":" + b1.a + ":" + b1.b);

  }
}

