using System;

static class Program
{

  static void Main (string[] args)
  {
    A a = new A(1);
    B b = new B(2,3);
    Console.WriteLine(a.a + ":" + b.a + ":" + b.b);
    a.foo();
    b.foo();

    A c = new B(4,5);
    c.foo();

  }
}

