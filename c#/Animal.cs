using System;

namespace ConsoleApplication1{

  class Program {

    public static void Main(string[] args)
    {
      Animal spot = new Animal(15,10,"Spot","Woof");
      Console.WriteLine("{0} says {1}",spot.Name, spot.sound);
      Console.WriteLine(spot.ToString());
      Console.WriteLine("Number of Animals: " + Animal.GetNumOfAnimals());
      Console.WriteLine(spot.GetSum(3,4));
      Console.WriteLine(spot.GetSum(num2:3.3,num1:4.4));

      // calls default ctor and *then* initializes data members
      Animal grover = new Animal
      {
        name = "Grover",
        height = 16,
        weight = 18,
        sound = "Grrr"
      };

      Console.WriteLine(grover.ToString());
      Console.WriteLine("Number of Animals: " + Animal.GetNumOfAnimals());

      Dog spike = new Dog(20,15,"Spike","woaf woaf","chicken");

      Console.WriteLine(spike.ToString());
    }
  }


  public class Animal {

    public double height{get;set;}
    public double weight{get;set;}
    public string sound{get;set;}

    public string name;

    public string Name
    {
      get{return name;}
      set{name = value;}
    }

    public Animal()
    {
      Console.WriteLine("Default ctor is running");
      this.height = 0;
      this.weight = 0;
      this.sound = "No Sound";
      this.name = "No Mame";
      ++numOfAnimals;
    }

    public Animal(double height, double weight, string name, string sound)
    {
      Console.WriteLine("Ctor is running");
      this.height = height;
      this.weight = weight;
      this.sound = sound;
      this.name = name;
      ++numOfAnimals;
    }

    private static int numOfAnimals = 0;

    public override string ToString()
    {
      return String.Format("{0} is {1} inches tall, weighs {2} lbs and likes to say {3}", name, height, weight, sound);
    }

    public static int GetNumOfAnimals()
    {
      return numOfAnimals;
    }

    public int GetSum(int num1 = 1, int num2 = 1)
    {
      return num1 + num2;
    }

    public double GetSum(double num1 = 1, double num2 = 1)
    {
      return num1 + num2;
    }
  }


  public class Dog : Animal
  {
    public string favFood{get;set;}

    public Dog() : base()
    {
      this.favFood = "No favorite food";
    }

    public Dog(double height, double weight, string name, string sound, string favFood)
      : base (height,weight,name,sound)
    {
        this.favFood = favFood;
    }

    public override string ToString()
    {
      return String.Format("{0} is {1} inches tall, weighs {2} lbs and likes to say {3} and eats {4}", name, height, weight, sound, favFood);
    }
  }

  public abstract class Shape
  {
    public abstract double area();
    public void foo()
    {
      Console.WriteLine("Hello");
    }
  }

  public interface ShapeItem
  {
    double area();
  }

  public class Rectangle : Shape
  {
    public override double area()
    {
      throw new NotImplementedException();
    }

  }



}
