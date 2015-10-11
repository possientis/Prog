using System;

namespace ConsoleApplication1
{
  static class Program
  {

    static void Main ()
    {


      // Circle c(2,0,0); in C++
      Circle c = new Circle(1,0,0);
      Console.WriteLine(c.Area);
      Console.WriteLine(c.Circumference);
      Console.WriteLine(c.GetHashCode());
      Console.WriteLine(c.GetType());

    }
  }
}

