
val l = List(5,0,7,3,4)
val words = List("the","quick","brown","fox")

// map
println(l map (_+1))          // List(6, 1, 8, 4, 5)
println(words map (_.length)) // List(3, 5, 5, 3)
println(words map (_.toList.reverse.mkString(""))) // List(eht, kciuq, nworb, xof)



