using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace ConsoleApplication1
{
  class Program
  {
    static void Main(string[] args)
    {

      A a = new A(2);
      A b = new A(5);

      A c = a + b;
      c += new A(6);  // coming for free in C# (contrary to C++)

      Console.WriteLine(c.a);

    }
  }

  public class A{
    public int a;
    public A(int a){this.a = a;}
    public static A operator+(A x, A y){
      return new A(x.a + y.a);
    }
  }

}
