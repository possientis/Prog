using System;

interface IShape {
  void draw();
} 

abstract class AbstractShape : IShape {
  abstract public void draw();
  public enum COLOR {RED,GREEN,BLUE};
  protected static string AsString(COLOR color){
    switch(color){
      case COLOR.RED:
        return "red";
      case COLOR.GREEN:
        return "green";
      case COLOR.BLUE:
        return "blue";
      default:
        return "unknown color";
    }
  }
  protected COLOR mColor;
}

class Rectangle : AbstractShape {
  public Rectangle(AbstractShape.COLOR color){mColor = color;}
  public override void draw(){
    Console.WriteLine("Drawing " + AsString(mColor) + " rectangle");
  }
}

class Square : AbstractShape {
  public Square(AbstractShape.COLOR color){mColor = color;}
  public override void draw(){
    Console.WriteLine("Drawing " + AsString(mColor) + " square");
  }
}

class Circle : AbstractShape {
  public Circle(AbstractShape.COLOR color){mColor = color;}
  public override void draw(){
    Console.WriteLine("Drawing " + AsString(mColor) + " circle");
  }
}

// using the template method pattern here, as the actual
// behaviour of 'GetShape' will be defined via specialization
// of virtual method GetColor through subclassing
abstract class AbstractShapeFactory {
  abstract public AbstractShape.COLOR GetColor();
  public IShape GetShape(String shapeType){
   if(shapeType == null){
    return null;
   }
   if(shapeType.Equals("CIRCLE", StringComparison.OrdinalIgnoreCase)){
     return new Circle(GetColor());
   } else if(shapeType.Equals("RECTANGLE", StringComparison.OrdinalIgnoreCase)){
     return new Rectangle(GetColor());
   } else if(shapeType.Equals("SQUARE", StringComparison.OrdinalIgnoreCase)){
     return new Square(GetColor());
   } 

   return null;
  }
}

// However the benefit of subclassing over maintaining
// 'mColor' state in base class is not that clear in this simple case
// It is propably beneficial when the distinction between various
// families of widgets (IShape) goes well beyond color difference.
class RedShapeFactory : AbstractShapeFactory {
  public override AbstractShape.COLOR GetColor(){return AbstractShape.COLOR.RED;}
}

class GreenShapeFactory : AbstractShapeFactory {
  public override AbstractShape.COLOR GetColor(){return AbstractShape.COLOR.GREEN;}
}

class BlueShapeFactory : AbstractShapeFactory {
  public override AbstractShape.COLOR GetColor(){return AbstractShape.COLOR.BLUE;}
}

// Factory of factories. The Abstract Factory design pattern is a case
// of Factory design pattern applied to various factory types.
class FactoryProducer {
  public AbstractShapeFactory GetFactory(String factoryType){
    if(factoryType == null){
      return null;
    }
    if(factoryType.Equals("RED",StringComparison.OrdinalIgnoreCase)){
      return new RedShapeFactory();
    } else if(factoryType.Equals("GREEN",StringComparison.OrdinalIgnoreCase)){
      return new GreenShapeFactory();
    } else if(factoryType.Equals("BLUE", StringComparison.OrdinalIgnoreCase)){
      return new BlueShapeFactory();
    }
    return null;
  }
}


public class AbstractFactory {

  public static void Main(string[] args){

    FactoryProducer producer = new FactoryProducer();

    // producing set of red widgets
    AbstractShapeFactory redFactory = producer.GetFactory("Red");
    IShape shape1 = redFactory.GetShape("CIRCLE");
    shape1.draw();
    IShape shape2 = redFactory.GetShape("RECTANGLE");
    shape2.draw();
    IShape shape3 = redFactory.GetShape("SQUARE");
    shape3.draw();

    // producing set of green widgets
    AbstractShapeFactory greenFactory = producer.GetFactory("Green");
    IShape shape4 = greenFactory.GetShape("CIRCLE");
    shape4.draw();
    IShape shape5 = greenFactory.GetShape("RECTANGLE");
    shape5.draw();
    IShape shape6 = greenFactory.GetShape("SQUARE");
    shape6.draw();

    // producing set of blue widgets
    AbstractShapeFactory blueFactory = producer.GetFactory("Blue");
    IShape shape7 = blueFactory.GetShape("CIRCLE");
    shape7.draw();
    IShape shape8 = blueFactory.GetShape("RECTANGLE");
    shape8.draw();
    IShape shape9 = blueFactory.GetShape("SQUARE");
    shape9.draw();

 }
}
