using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace ConsoleApplication1
{
  public class Dog
  {
    static int numLegs = 4;
    public int age;
    public string name;
    public string breed;


    public Dog()
    {
      age = 0;
      name = "";
      breed = "";
    }

    public Dog(int age, string name, string breed)
    {
      this.age = age;
      this.name = name;
      this.breed = breed;
    }

    public void Bark()
    {
      Console.WriteLine(this.name + " says woof woof!");
      Console.WriteLine("I have " + Dog.numLegs + " legs");
    }
  }
}


