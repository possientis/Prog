// Bridge design pattern

// bridge implementation interface
abstract class DrawAPI {
  def drawCircle(radius: Int, x: Int, y: Int)
}


// concrete bridge implementation classes implementing DrawAPI interface
class RedCircle extends DrawAPI {
  def drawCircle(radius: Int, x: Int, y: Int) = {
   println("Drawing Circle[ color: red  , radius: "+radius+", x: "+x+", y: "+y+"]")
  } 
}

class GreenCircle extends DrawAPI {
  def drawCircle(radius: Int, x: Int, y: Int) = {
   println("Drawing Circle[ color: green, radius: "+radius+", x: "+x+", y: "+y+"]")
  } 
}


// create an abstract class Shape using the DrawAPI interface.
abstract class Shape(drawAPI: DrawAPI) {
  def draw()
}

// create concrete class implementing the Shape interface (abstract class)
class Circle(x: Int, y: Int, radius: Int, drawAPI: DrawAPI)
  extends Shape(drawAPI) {
  def draw() = {
    drawAPI.drawCircle(radius,x,y)
  }
}

// Use Shape and DrawAPI classes to draw different colored circles
object Bridge {
  def main(args: Array[String]) = {
    // implementation of concrete circles selected at run time.
    val redCircle = new Circle(100, 100, 10, new RedCircle)
    val greenCircle = new Circle(100, 100, 10, new GreenCircle)
    redCircle.draw()
    greenCircle.draw()
  }
}
