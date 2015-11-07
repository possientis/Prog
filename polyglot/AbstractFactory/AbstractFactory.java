// the Abstract Factory pattern looks like the factory pattern 
// applied to the production of various factories

interface IShape {
  void draw();
}

abstract class AbstractShape implements IShape {
  @Override
  abstract public void draw();
  public enum COLOR {RED,GREEN,BLUE};
  protected static final String asString(COLOR color){
    switch(color){
      case RED:
        return "red";
      case GREEN:
        return "green";
      case BLUE:
        return "blue";
      default:
        return "unknown color";
    }
  }
  protected COLOR mColor;
}

class Rectangle extends AbstractShape {
  public Rectangle(AbstractShape.COLOR color){mColor = color;}
  public void draw() {
    System.out.println("Drawing " + asString(mColor) + " rectangle");
  }
}

class Square extends AbstractShape {
  public Square(AbstractShape.COLOR color){mColor = color;}
  public void draw() {
    System.out.println("Drawing " + asString(mColor) + " square");
  }
}

class Circle extends AbstractShape {
  public Circle(AbstractShape.COLOR color){mColor = color;}
  public void draw() {
    System.out.println("Drawing " + asString(mColor) + " circle");
  }
}

// using the template method pattern here, as the actual
// behaviour of 'getShape' will be defined via specialization
// of virtual method getColor through subclassing
abstract class AbstractShapeFactory {
  abstract public AbstractShape.COLOR getColor();
  public IShape getShape(String shapeType){
    if(shapeType == null){
      return null;
    }
    if(shapeType.equalsIgnoreCase("CIRCLE")){
      return new Circle(getColor());
    } else if(shapeType.equalsIgnoreCase("RECTANGLE")){
      return new Rectangle(getColor());
    } else if(shapeType.equalsIgnoreCase("SQUARE")){
      return new Square(getColor());
    }
    return null;
  }
}

// However the benefit of subclassing over maintaining
// 'mColor' state in base class is not that clear in this simple case
// It is propably beneficial when the distinction between various
// families of widgets (IShape) goes well beyond color difference.
class RedShapeFactory extends AbstractShapeFactory {
  public AbstractShape.COLOR getColor(){return AbstractShape.COLOR.RED;}
}

class GreenShapeFactory extends AbstractShapeFactory {
  public AbstractShape.COLOR getColor(){return AbstractShape.COLOR.GREEN;}
}

class BlueShapeFactory extends AbstractShapeFactory {
  public AbstractShape.COLOR getColor(){return AbstractShape.COLOR.BLUE;}
}

// Factory of factories. The Abstract Factory design pattern is a case
// of Factory design pattern applied to various factory types.
class FactoryProducer {
  public AbstractShapeFactory getFactory(String factoryType){
    if(factoryType == null){
      return null;
    }
    if(factoryType.equalsIgnoreCase("RED")){
      return new RedShapeFactory();
    } else if(factoryType.equalsIgnoreCase("GREEN")){
      return new GreenShapeFactory();
    } else if(factoryType.equalsIgnoreCase("BLUE")){
      return new BlueShapeFactory();
    }
    return null;
  }
}

public class AbstractFactory {

  public static void main(String[] args){
    FactoryProducer producer = new FactoryProducer();
    // producing set of red widgets
    AbstractShapeFactory redFactory = producer.getFactory("Red");
    IShape shape1 = redFactory.getShape("CIRCLE");
    IShape shape2 = redFactory.getShape("RECTANGLE");
    IShape shape3 = redFactory.getShape("SQUARE");
    shape1.draw();
    shape2.draw();
    shape3.draw();

    // producing set of green widgets
    AbstractShapeFactory greenFactory = producer.getFactory("Green");
    IShape shape4 = greenFactory.getShape("CIRCLE");
    IShape shape5 = greenFactory.getShape("RECTANGLE");
    IShape shape6 = greenFactory.getShape("SQUARE");
    shape4.draw();
    shape5.draw();
    shape6.draw();

    // producing set of blue widgets
    AbstractShapeFactory blueFactory = producer.getFactory("Blue");
    IShape shape7 = blueFactory.getShape("CIRCLE");
    IShape shape8 = blueFactory.getShape("RECTANGLE");
    IShape shape9 = blueFactory.getShape("SQUARE");
    shape7.draw();
    shape8.draw();
    shape9.draw();
  }
}


