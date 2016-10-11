// Singleton design pattern
object SingleObject {
  def getInstance() = SingleObject
  def showMessage() = println("The single object is alive and well")
}

object Singleton {
  def main(args: Array[String]) = {
    val object1 = SingleObject.getInstance()
    object1.showMessage()
    
    val object2 = SingleObject.getInstance()
    if(object1 eq object2){
      println("The two objects are the same")
    }
  }
}
