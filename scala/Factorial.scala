
object Factorial {

  def fact(n: Int) = (1 to n).foldLeft(1) {_ * _}

  def main(args: Array[String]){
    println(fact(5))
  }
}
