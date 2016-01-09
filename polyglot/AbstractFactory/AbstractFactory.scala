// Abstract Factory design pattern
// the Abstract Factory pattern looks like the factory pattern 
// applied to the production of various factories

abstract class Shape {
  def draw()
}

abstract class AbstractShape(val color: AbstractShape.Color.Color) extends Shape {
}

object AbstractShape {
  // http://www.scala-lang.org/api/current/scala/Enumeration.html
  object Color extends Enumeration {
    type Color = Value            // needed to 'Color' can be used as a type
    val RED, GREEN, BLUE = Value  // '= Value' ??? what is that?  
  }
  
  import Color._
  def asString(color: Color): String = {
    color match {
      case RED    => "red"
      case GREEN  => "green"
      case BLUE   => "blue"
      case _      => "unknown color"
    }  
  }
}


class Rectangle(override val color: AbstractShape.Color.Color) 
  extends AbstractShape (color) {
  import AbstractShape._
  def draw() = {
    println("Drawing %s rectangle" format asString(color))
  }
}

class Square(override val color: AbstractShape.Color.Color) 
  extends AbstractShape (color) {
  import AbstractShape._
  def draw() = {
    println("Drawing %s square" format asString(color))
  }
}

class Circle(override val color: AbstractShape.Color.Color) 
  extends AbstractShape (color) {
  import AbstractShape._
  def draw() = {
    println("Drawing %s circle" format asString(color))
  }
}

object AbstractFactory {
  import AbstractShape.Color._
 
  def main(args: Array[String]) = {
  }
}

