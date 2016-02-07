import scala.collection.mutable.HashMap
// += is a method on HashMap
// -> is a method on 1,2,3 returning a tuple
val treasureMap = new HashMap[Int, String]
treasureMap += (1 -> "Go to island.")
treasureMap += (2 -> "Find big X on ground.")
treasureMap += (3 -> "Dig.")
println(treasureMap(2))


// factory method for immutable Map (no import needed)
// factory method is actually 'apply' of companion object Map
val romanNumeral = Map(
1 -> "I",
2 -> "II",
3 -> "III",
4 -> "IV",
5 -> "V"
)


println(romanNumeral)
