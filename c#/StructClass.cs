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

      Console.WriteLine("class A:");
      A a = new A(10);
      Console.WriteLine(a.a);
      DoStuff(a);
      Console.WriteLine(a.a);
      Console.WriteLine("struct B:");
      B b = new B(10);
      Console.WriteLine(b.a);
      DoStuff(b);
      Console.WriteLine(b.a);


    }


    public static void DoStuff(A x){
      x.a = 5;
    }

    public static void DoStuff(B x){
      x.a = 5;
    }


  }

  class A{
    public int a;
    public A(int a){this.a = a;}
  }

  struct B{
    public int a;
    public B(int a){this.a = a;}
  }

}
