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
