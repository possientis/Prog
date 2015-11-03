using System;
using System.Collections;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Diagnostics;

namespace ConsoleApplication1
{
  class Program
  {
    static void Main(string[] args)
    {
      A a = new A();
      B b = new B();
      A c = new B(); // attempting to use polymorphism

      a.foo();
      b.foo();
      c.foo();  // A::foo not B::foo as hiding rather than virtual
      c.bar();  // B::bar (virtual)

    }

  }

  class A {
    public void foo(){
      Console.WriteLine("A::foo() is running");
    }
    public virtual void bar(){
      Console.WriteLine("A::bar() is running");
    }
  }

  class B : A{
    new public void foo(){ // hiding base method
      Console.WriteLine("B::foo() is running");
    }
    override public void bar(){
      Console.WriteLine("B::bar() is running");
    }
  }
}

      /*
      Stopwatch stop = new Stopwatch();
      stop.Start();
      stop.Stop();


      stop.Restart();
      stop.Stop();
      Console.WriteLine(stop.Elapsed);
      */
 
