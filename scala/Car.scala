object Test{
  def main(args: Array[String]){
    println("Hello World!")
  
    val car1 = new Car(2013,0)
    println(car1.year)
    
    val car2 = Car.create(2014);
    println(car2.year)

    val car3 = Car(2015)
    println(car3.year)

    val prices = List(10, 15, 20, 25, 30, 35, 40)

  }
}

class Car(val year : Int, var miles : Int)
object Car {
  def create(year : Int) = new Car(year, 0)
  def apply(year : Int) = new Car(year, 0) // apply has special meaning
}

trait Friend {
  val name : String
  def listen() = println("I am " + name + " listening")
}

class Human(val name : String) extends Friend
class Animal(val name :String)

class Dog(val name : String) extends Animal(name){
}

println("hello")

//buddy.listen()
