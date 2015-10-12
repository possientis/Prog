using System;

namespace ConsoleApplication1
{
  static class Program
  {

    static void Main (string[] args)
    {


      Animal a = new Animal("bob", 10);
      Animal b = new Animal();
      Dog c = new Dog("doggy", 12, "spaniel");

      b.Name = "harry";
      b.Age = 12;

      Console.WriteLine(a.Name + ":" + b.Name + ":" + c.Name);

      Dog d = new Dog();

      d.Breed = "shepperd";
      d.Name = "woolfy";
      d.Age = 5;

      Animal e = new Dog("gary", 8, "abc");
      e.Speak();


    }
  }
}

