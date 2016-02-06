object Test {
  def main(args: Array[String]){
    val greetStrings = new Array[String](3)
    greetStrings(0) = "Hello"
    greetStrings(1) = ", "
    greetStrings(2) = "world! \n"
    for (i <- 0 to 2){
      print(greetStrings(i))
    }
    
  }
}

