import math._

object Test {
  def main(args: Array[String]){
    val dog = new Dog("Bill")
    dog foo "hello...."
    val x = dog foo _
    x("hihi")
  }

}

class Dog(name: String){
  def foo(stuff: String) = {
    println(name + " says " + stuff)
  }
}
