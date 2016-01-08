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




object Factory {
  def main(args: Array[String]){
    val x = new Rectangle
    x.draw
  }
}
