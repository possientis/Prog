// does not compile, probably need a more recent version of scala
object MyExtensions {
  def main(args: Array[String]) = {
    println("Running my extensions")
  }

  implicit class IntPredicates(i: Int) {
    def isEven  = i % 2 == 0
    def isOdd   = !isEven 
  }
}



