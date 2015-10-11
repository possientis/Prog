using System;

namespace ConsoleApplication1
{
  public class Circle
  {

    public double radius;
    public double x;
    public double y;


    // need to use keyword 'override' to override base class 'object' impl
    public override string ToString()
    {
      return "< Circle: radius = "+radius+": center = ("+x+","+y+") >";
    }


    public double Circumference
    {
      get
      {
        return 2 * Math.PI * radius;

      }
    }

    public double Area
    {
      get
      {
        return Math.PI * radius * radius;
      }
    }

    // property: 3 new keywords, get, set, value
    public double Diameter
    {
      get
      {
        return radius * 2.0;
      }
      set
      {
        radius = value/2.0;    // specific C# feature
      }
    }


    public Circle()
    {
      radius = 0.0f;
      x = 0.0f;
      y = 0.0f;
    }

    public Circle(float radius, float x, float y)
    {
      this.radius = radius;
      this.x = x;
      this.y = y;
    }
  }
}
