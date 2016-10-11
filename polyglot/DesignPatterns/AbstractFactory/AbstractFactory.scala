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

// using the template method pattern here, as the actual
// behaviour of 'getShape' will be defined via specialization
// of virtual method getColor through subclassing
abstract class AbstractShapeFactory {
  def getColor(): AbstractShape.Color.Color
  def getShape(shapeType: String): Shape = {
    if(shapeType == null) return null

    if(shapeType.equalsIgnoreCase("CIRCLE")){
      return new Circle(getColor())
    } else if(shapeType.equalsIgnoreCase("RECTANGLE")){
      return new Rectangle(getColor())
    } else if(shapeType.equalsIgnoreCase("SQUARE")){
      return new Square(getColor())
    }
    return null
  }
}

// However the benefit of subclassing over maintaining
// 'mColor' state in base class is not that clear in this simple case
// It is propably beneficial when the distinction between various
// families of widgets (Shape) goes well beyond color difference.
class RedShapeFactory extends AbstractShapeFactory {
  def getColor() = AbstractShape.Color.RED 
}

class GreenShapeFactory extends AbstractShapeFactory {
  def getColor() = AbstractShape.Color.GREEN 
}

class BlueShapeFactory extends AbstractShapeFactory {
  def getColor() = AbstractShape.Color.BLUE 
}

// Factory of factories. The Abstract Factory design pattern is a case
// of Factory design pattern applied to various factory types.
class FactoryProducer {
  def getFactory(factoryType: String): AbstractShapeFactory = {
    if(factoryType == null) return null
    if(factoryType.equalsIgnoreCase("RED")){
      return new RedShapeFactory
    } else if(factoryType.equalsIgnoreCase("GREEN")){
      return new GreenShapeFactory
    } else if(factoryType.equalsIgnoreCase("BLUE")){
      return new BlueShapeFactory
    }
    return null
  }
}

object AbstractFactory {
  import AbstractShape.Color._
 
  def main(args: Array[String]) = {
    val producer = new FactoryProducer
    // producing set of red widgets
    val redFactory = producer.getFactory("Red")
    val shape1 = redFactory.getShape("CIRCLE")
    val shape2 = redFactory.getShape("RECTANGLE")
    val shape3 = redFactory.getShape("SQUARE")
    shape1.draw()
    shape2.draw()
    shape3.draw()

    // producing set of green widgets
    val greenFactory = producer.getFactory("Green")
    val shape4 = greenFactory.getShape("CIRCLE")
    val shape5 = greenFactory.getShape("RECTANGLE")
    val shape6 = greenFactory.getShape("SQUARE")
    shape4.draw()
    shape5.draw()
    shape6.draw()
 
    // producing set of blue widgets
    val blueFactory = producer.getFactory("Blue")
    val shape7 = blueFactory.getShape("CIRCLE")
    val shape8 = blueFactory.getShape("RECTANGLE")
    val shape9 = blueFactory.getShape("SQUARE")
    shape7.draw()
    shape8.draw()
    shape9.draw()
  }
}

