object MapTest {
  def main(args: Array[String]){
    val m = Map(1 -> 2, 2 -> 4, 3 -> 6)
    println(m.toList)
    println(m.mapValues(v => v * 2))
    println(m.toList.map {case (k,v) => k})
  }
}
