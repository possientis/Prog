using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace ConsoleApplication1
{
  public class Cat
  {

    public string name;
    public int numLives;
    public bool isAlive;


    public Cat(string name)
    {
      Console.WriteLine("Cat constructor running..");
      this.name = name;
      numLives = 9;
      isAlive = true;
    }

    public Cat(): this("")  // calling constructor Cat(string)
    {
    }


    public void Die()
    {
      if(numLives > 0)
      {
        --numLives;
      }
      if(numLives == 0)
      {
        isAlive = false;
      }
    }

    public void Meow()
    {
      if(isAlive)
      {
        Console.WriteLine("Meow! Meow!");
      }
      else
      {
        Console.WriteLine("I am dead");
      }
    }
 }
}


