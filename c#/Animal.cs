using System;
using System.Collections.Generic;   // List<K>
using System.Linq;  // List<K>.Where

namespace ConsoleApplication1{

  class Program {


    delegate double  GetSum(double num1, double num2);

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

      Rectangle rect1 = new Rectangle(2.0,3.0);
      Console.WriteLine("Area of rectangle is: " + rect1.Area());

      Rectangle rect2 = new Rectangle(5.0,1.0);

      Shape rect3 = rect1 + rect2;  // rect3 declared as Shape, why not... not using '+' on it
      Console.WriteLine("Area of new rectangle is: " + rect3.Area());

      Triangle tria = new Triangle(5.0,10.0);
      Console.WriteLine("Area of triangle is: " + tria.Area());

      KeyValue <string,int> myPair = new KeyValue<string,int>("abc",23);
      Console.WriteLine(myPair.ToString());


      Temperature micTemp = Temperature.Warm;

      switch(micTemp){
        case Temperature.Low:
          Console.WriteLine("Temperature is low");
          break;
        default:
          Console.WriteLine("Temperature is anything but low");
          break;  // need a break here for some reason
      }

      int fact = 6;

      GetSum sum = delegate(double num1, double num2)
      {
        return num1 + num2 + fact;
      };  // need a ';' here for some reason

      GetSum sum2 = sum;

      Console.WriteLine("fact + 5 + 10 = " + sum2(5,10));

      Func<int,int,int> myLambda = (x,y) => x + y;
      Console.WriteLine("5 + 3 = " + myLambda.Invoke(5,3));

      List<int> seq = new List<int> {5,10,15,20,25};

      List<int> odd = seq.Where(n => (n % 2) == 1).ToList();

      foreach(int num in odd)
      {
        Console.WriteLine(num);
      }

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
    public abstract double Area();

    public void Foo()
    {
      Console.WriteLine("Hello");
    }
  }

  public interface ShapeItem
  {
    double Area();
  }


  public class Rectangle : Shape
  {
    private double length;
    private double width;

    public Rectangle(double length, double width)
    {
      this.length = length;
      this.width = width;
    }

    public override double Area()
    {
      return length * width;
    }

    public static Rectangle operator+(Rectangle rect1, Rectangle rect2)
    {
      double rectLength = rect1.length + rect2.length;
      double rectWidth = rect1.width + rect2.width;

      return new Rectangle(rectLength, rectWidth);
    }
  }

  public class Triangle : Shape
  {
    private double width;
    private double height;

    public Triangle(double width, double height)
    {
      this.width = width;
      this.height = height;
    }

    public override double Area()
    {
      return 0.5 * width * height;
    }
  }


  public class KeyValue<TKey,TValue>
  {

    public TKey key{get;set;}
    public TValue val {get;set;}

    public KeyValue(TKey k, TValue v)
    {
      key = k;
      val = v;
    }

    public override string ToString()
    {
      return "(" + key.ToString() + "," + val.ToString() + ")";
    }
  }

  public enum Temperature
  {
    Freeze,
    Low,
    Warm,
    Boil
  }





}
