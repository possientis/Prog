// Bridge design pattern

// bridge implementation interface
interface DrawAPI {
  public void drawCircle(int radius, int x, int y);
}

// concrete bridge implementation classes implementing DrawAPI interface
class RedCircle implements DrawAPI {
  @Override
  public void drawCircle(int radius, int x, int y){
    System.out.println(
        "Drawing Circle[ color: red  , radius: "+radius+", x: "+x+ ", y: "+y+"]"
    );
  }
}

class GreenCircle implements DrawAPI {
  @Override
  public void drawCircle(int radius, int x, int y){
    System.out.println(
        "Drawing Circle[ color: green, radius: "+radius+", x: "+x+ ", y: "+y+"]"
    );
  }
}

// create an abstract class Shape using the DrawAPI interface.
abstract class Shape {
  protected DrawAPI drawAPI;
  protected Shape(DrawAPI drawAPI){this.drawAPI = drawAPI;}
  public abstract void draw();  // abstraction need not follow implementation API
}

// create concrete class implementing the Shape interface (abstract class)
class Circle extends Shape {
  private int x, y, radius;
  public Circle(int x, int y, int radius, DrawAPI drawAPI){
    super(drawAPI);
    this.x = x;
    this.y = y;
    this.radius = radius;
  }
  @Override
  public void draw(){
    drawAPI.drawCircle(radius,x,y);
  }
}

// Use Shape and DrawAPI classes to draw different colored circles
public class Bridge {
  public static void main(String[] args){
    // implementation of concrete circles selected at run time.
    Shape redCircle = new Circle(100, 100, 10, new RedCircle());
    Shape greenCircle = new Circle(100, 100, 10, new GreenCircle());
    redCircle.draw();
    greenCircle.draw();
  }
}
