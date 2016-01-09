// Factory design pattern

abstract class Shape{
  def draw()
}

class Rectangle extends Shape {
  def draw(){
    println("Inside Rectangle::draw() method.")
  }
}

class Square extends Shape {
  def draw(){
    println("Inside Square::draw() method.")
  }
}

class Circle extends Shape {
  def draw(){
    println("Inside Circle::draw() method.")
  }
}

class ShapeFactory {
  // use getShape methid to get object of type Shape
  def getShape(shapeType: String): Shape = {
    if(shapeType == null) return null

    if(shapeType.equalsIgnoreCase("CIRCLE")){
      return new Circle()
    } else if(shapeType.equalsIgnoreCase("RECTANGLE")){
      return new Rectangle()
    } else if(shapeType.equalsIgnoreCase("SQUARE")){
      return new Square();
    }

    return null; 
    
  }
}


object Factory {
  def main(args: Array[String]){
    val shapeFactory = new ShapeFactory()
    
    // get an object of type Circle and call its draw method
    val shape1 = shapeFactory.getShape("CIRCLE")
    shape1.draw()

    // get an object of type Rectangle and call its draw method
    val shape2 = shapeFactory.getShape("RECTANGLE")
    shape2.draw()

    // get an object of type Square and call its draw method
    val shape3 = shapeFactory.getShape("SQUARE")
    shape3.draw()
  }
}




