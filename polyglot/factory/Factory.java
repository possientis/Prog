interface IShape {
  void draw();
}

class Rectangle implements IShape {

  public void draw() {
    System.out.println("Inside Rectangle::draw() method.");
  }
}

class Square implements IShape {

  public void draw() {
    System.out.println("Inside Square::draw() method.");
  }
}

class Circle implements IShape {

  public void draw() {
    System.out.println("Inside Circle::draw() method.");
  }
}

class ShapeFactory {
  // use getShape method to get object of type IShape
  public IShape getShape(String shapeType){

    if(shapeType == null){
      return null;
    }

    if(shapeType.equalsIgnoreCase("CIRCLE")){
      return new Circle();
    } else if(shapeType.equalsIgnoreCase("RECTANGLE")){
      return new Rectangle();
    } else if(shapeType.equalsIgnoreCase("SQUARE")){
      return new Square();
    }

    return null;
  }
}

public class Factory {

  public static void main(String[] args){
    ShapeFactory shapeFactory = new ShapeFactory();

    // get an object of Circle and call its draw method.
    IShape shape1 = shapeFactory.getShape("CIRCLE");
    shape1.draw();

    // get an object of Rectangle and call its  draw method
    IShape shape2 = shapeFactory.getShape("RECTANGLE");
    shape2.draw();

    // get an object of Square and call its  draw method
    IShape shape3 = shapeFactory.getShape("SQUARE");
    shape3.draw();

  }

}


