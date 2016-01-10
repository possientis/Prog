// Prototype design pattern
// Imagine that in order to instantiate certain objects we need to carry out
// expensive database queries. In order to improve performance, it would 
// be beneficial to cache whatever object is created from the database
// and return a copy of the cached object whenever a subsequent request
// for object instantiation arises.

import scala.collection.immutable._ // HashMap[K,V]

abstract class Shape extends Cloneable {
  var id: String = null
  def draw()
  def getId(): String = id
  def setId(id:String) = {this.id = id}
  
  override def clone(): Object = { super.clone() }
}

class Rectangle extends Shape {
  def draw() = println("Inside Rectangle::draw() method.")
}

class Square extends Shape {
  def draw() = println("Inside Square::draw() method.")
}

class Circle extends Shape {
  def draw() = println("Inside Circle::draw() method.")
}

class PrototypeManager {
  var shapeMap = new HashMap[String, Shape]
  def getShape(shapeId: String): Shape = {
    val Some(cachedShape) = shapeMap.get(shapeId)
    return cachedShape.clone().asInstanceOf[Shape]
  }
  def loadCache() = {
    val rect = new Rectangle
    rect.setId("1")
    shapeMap += ("1" -> rect)
    
    val square = new Square
    square.setId("2")
    shapeMap += ("2" -> square)

    val circle = new Circle
    circle.setId("3")
    shapeMap += ("3" -> circle)
  } 
}

object Prototype {
  def main(args: Array[String]) = {
    // new a prototype manager
    val manager = new PrototypeManager
    // prototype manager registers a few prototypes
    manager.loadCache()
    // prototype manager can now be used as factory object
    val clonedShape1 = manager.getShape("1")
    clonedShape1.draw()
    
    val clonedShape2 = manager.getShape("2")
    clonedShape2.draw()

    val clonedShape3 = manager.getShape("3")
    clonedShape3.draw()
  }
}
