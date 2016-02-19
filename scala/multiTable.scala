def printMultiTable() {
  for (i <- 1 to 10) {
    for (j <- 1 to 10) {
      val prod = (i * j).toString
      print(String.format("%4s", prod))
    }
      println()
  }
}
printMultiTable()

// more functional style, using yield
// yield makes a collection, the method mkString creates a string from it
def multiTable = {
  val table = for (i <- 1 to 10) yield {
    val row = for (j <- 1 to 10) yield {
      val prod = (i * j).toString
      // second yield refers to this line
      String.format("%4s", prod)
    }
    // first yield refers to this
    row.mkString + '\n'
  }
  table.mkString
}
// this code seggregates the purely functional part from the
// code with side effect.
println(multiTable)
