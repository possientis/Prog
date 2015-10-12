using System;

namespace ConsoleApplication1
{
  public class Animal{

    string name;
    int age;

    public Animal(string name, int age){
      this.name = name;
      this.age = age;
      Console.WriteLine("Animal constructor running...");
    }

    public Animal():this("",0){}

    public virtual void Speak()
    {
      Console.WriteLine(Name + " says I can't speak I am an animal!");
    }

    public string Name
    {
      get{return name;}
      set{name = value;}
    }
    public int Age

    {
      get{return age;}
      set{age = value;}
    }
  }
}
