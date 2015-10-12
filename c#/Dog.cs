using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace ConsoleApplication1
{
  public class Dog : Animal
  {
    private string breed;

    public Dog(string name, int age, string breed) : base(name,age)
    {
      Console.WriteLine("Dog constructor running...");
      this.breed = breed;
    }

    public Dog() : base()
    {
      Console.WriteLine("Dog default constructor running...");
      this.breed = "";
    }

    public override void Speak()
    {
      Console.WriteLine(Name + " says woof woof");
    }

    public string Breed
    {
      get{return breed;}
      set{breed = value;}
    }
  }
}


