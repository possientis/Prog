import scala.collection.mutable
val words = mutable.Set.empty[String]
words += "hello"    // adding to a set
words += "there"
words += "there"

println(words)  // Set(hello, there)

val text = "See Spot run. Run, Spot, Run!"
for(w <- text.split("[ !,.]+")) // regex , regular expression
  println(w)

words -= "hello"    // removing from a set
words -= "there"
println(words)      // Set()

for(w <- text.split("[ !,.]+"))
  words += w.toLowerCase()

println(words)      // Set(run, see, spot)

words ++= List("do", "re", "mi")  // adding multiple objects to set
println(words)                    // Set(re, run, do, mi, see, spot)
words --= List("do", "re", "fa")  // removing multiple objects from set
println(words)                    // Set(run, mi, see, spot)

println(words.size)               // 4 size of a set
println(words.contains("mi"))     // true membership of a set

val map = mutable.Map.empty[String, Int]
println(map)        // Map()

map("hello") = 1    
map("there") = 2
println(map)              // Map(there -> 2, hello -> 1)
println(map("there"))     // 2

map += ("how" -> 5)
println(map)              // Map(there -> 2, hello -> 1, how -> 5)

map -= "how"
println(map)              // Map(there -> 2, hello -> 1)

map ++= List("how" -> 5, "are" -> 8, "you?" -> 12)
println(map)              // Map(you? -> 12, there -> 2, are -> 8, hello -> 1, how -> 5)

map --= List("how", "are", "you?")
println(map)                      // Map(there -> 2, hello -> 1)

println(map.size)                 // 2, size of map
println(map.contains("hello"))    // trueo

println(map.keys)                 // Set(there, hello)

def wordcounts(text: String) = {
  val counts = mutable.Map.empty[String,Int]
  for(rawWord <- text.split("[ !.,]+")) {
    val word = rawWord.toLowerCase
    val oldCount = 
      if (counts.contains(word))
        counts(word)
      else
        0
    counts += (word -> (oldCount + 1))
  }
  counts
}

println(text)               // See Spot run. Run, Spot, Run!
println(wordcounts(text))   // Map(spot -> 2, see -> 1, run -> 3)


val list1 = List(1, 2, 3)                       // initialize list, List.apply(...
println(list1)                                  // List(1, 2, 3)
val set1  = mutable.Set(1, 2, 3)                // initialize set
println(set1)                                   // Set(2, 1, 3)     
val map1 = mutable.Map(1->"there", 4->"hello")  // initialize map
println(map1)                                   // Map(4 -> hello, 1 -> there)
val arr1 = Array(1, 2, 3)                       // initialize array
println(arr1)                                   // [I@6d011211    oh well...


val stuff1 = mutable.Set(42)                    // compiler assumes Set[42]
//stuff1 += "abracadabra"                       // will fail

val stuff2 = mutable.Set[Any](42)               // explicit type
stuff2 += "abracadabra"                         // now succeeds
println(stuff2)                                 // Set(abracadabra, 42)


// Array        vs List   mutable vs immutable  -> x.toList
// mutable.Map  vs Map    mutable vs immutable  -> Map.empty ++ x
// mutable.Set  vs Set    mutable vs immutable  -> Set.empty ++ x

val original = Set(1, 2, 3) // immutable set
val updated = original + 5
println(updated)            // Set(1, 2, 3, 5)













