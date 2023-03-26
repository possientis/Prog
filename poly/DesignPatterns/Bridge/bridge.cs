// Bridge design pattern
using System;

// bridge implementation interface
interface DrawAPI {
  void DrawCircle(int radius, int x, int y);
}

// concrete bridge implementation classes implementing DrawAPI interface
class RedCircle : DrawAPI {
  public void DrawCircle(int radius, int x, int y){
    Console.WriteLine(
        "Drawing Circle[ color: red  , radius: "+radius+", x: "+x+ ", y: "+y+"]"
    );
  }
}

class GreenCircle : DrawAPI {
  public void DrawCircle(int radius, int x, int y){
    Console.WriteLine(
        "Drawing Circle[ color: green, radius: "+radius+", x: "+x+ ", y: "+y+"]"
    );
  }
}

// create an abstract class Shape using the DrawAPI interface.
abstract class Shape {
  protected DrawAPI drawAPI;
  protected Shape(DrawAPI drawAPI){this.drawAPI = drawAPI;}
  public abstract void Draw();  // abstraction need not follow implementation API
}

// create concrete class implementing the Shape interface (abstract class)
class Circle : Shape {
  private int x, y, radius;
  public Circle(int x, int y, int radius, DrawAPI drawAPI) : base(drawAPI){
    this.x = x;
    this.y = y;
    this.radius = radius;
  }
  public override void Draw(){
    drawAPI.DrawCircle(radius,x,y);
  }
}

// Use Shape and DrawAPI classes to draw different colored circles
public class Bridge {
  public static void Main(string[] args){
  // implementation of concrete circles selected at run time.
  Shape redCircle = new Circle(100, 100, 10, new RedCircle());
  Shape greenCircle = new Circle(100, 100, 10, new GreenCircle());
  redCircle.Draw();
  greenCircle.Draw();
  }
}




