using System;

interface IShape {
  void draw();
} 


class Rectangle : IShape {

  public void draw(){
    Console.WriteLine("Inside Rectangle::draw() method.");
  }
}

class Square : IShape {

  public void draw(){
    Console.WriteLine("Inside Square::draw() method.");
  }
}

class Circle : IShape {

  public void draw(){
    Console.WriteLine("Inside Circle::draw() method.");
  }
}

class ShapeFactory {
  
  // use GetShape method to get object of type IShape
  public IShape GetShape(string shapeType) {

   if(shapeType == null){
    return null;
   }

   if(shapeType.Equals("CIRCLE", StringComparison.OrdinalIgnoreCase)){
     return new Circle();
   } else if(shapeType.Equals("RECTANGLE", StringComparison.OrdinalIgnoreCase)){
     return new Rectangle();
   } else if(shapeType.Equals("SQUARE", StringComparison.OrdinalIgnoreCase)){
     return new Square();
   } 

   return null;

  }
  
} 

public class Factory {

  public static void Main(string[] args){
    ShapeFactory shapeFactory = new ShapeFactory();

    // get an object of Circle and call its draw method
    IShape shape1 = shapeFactory.GetShape("CIRCLE");
    shape1.draw();
 
    // get an object of Rectangle and call its draw method
    IShape shape2 = shapeFactory.GetShape("RECTANGLE");
    shape2.draw();

    // get an object of Square and call its draw method
    IShape shape3 = shapeFactory.GetShape("SQUARE");
    shape3.draw();



  }
}
