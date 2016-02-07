// you can change 'mutable' by 'immutable' but '+=' won't work
import scala.collection.mutable.HashSet


val jetSet = new HashSet[String]
jetSet += "Lear"
jetSet += ("Boeing", "Airbus")
println(jetSet.contains("Cessna"))


// 'Set' is factory method for immutable HashSet in companion object
// no need for import for that
val movieSet = Set("Hitch", "Poltergeist", "Shrek")
println(movieSet)
