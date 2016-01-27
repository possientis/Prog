// can be done in php (with traits) and Java (default method of interface)
object AbstractTraits {
  def main(args: Array[String]){
    val w = new MyHelloWorld(" world!");
    w.sayHelloWorld
  }
}

trait Hello {
  def sayHelloWorld = {
    println("Hello" + getWorld());
  } 
  def getWorld(): String;
}


class MyHelloWorld(world: String) extends Hello {
  def getWorld = world
}


