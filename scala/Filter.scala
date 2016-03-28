println(List(1,2,3,4,5) filter (_ % 2 == 0)) //  List(2, 4)

val words = List("the", "quick", "brown", "fox")
println(words filter (_.length == 3)) // List(the, fox)

// partition of a list returns a tuple
// xs partition p = (xs filter p(_), xs filter !p(_))

println(List(1,2,3,4,5) partition (_ % 2 == 0)) // (List(2, 4),List(1, 3, 5))

// the find method is like filter but returns first element, rather than whole list
println(List(1,2,3,4,5) find (_ % 2 == 0))  // Some(2)
println(List(1,2,3,4,5) find (_ <= 0))      // None

println(List(1,2,3,-4,5) takeWhile (_ > 0)) // List(1, 2, 3)
println(words dropWhile (_ startsWith "t")) // List(quick, brown, fox)

// xs span p = (xs takeWhile p, xs dropWhile p) , similar to splitAt wr take and drop
// like splitAt, span avoids traversing the list twice

println(List(1,2,3,-4,5) span (_ > 0)) // (List(1, 2, 3),List(-4, 5))


println(List(1,2,3,4,5) forall (_ > 0))   // true
println(List(1,2,3,-4,5) forall (_ > 0))  // false


println(List(1,2,3,4,5) exists (_ < 0))     // false
println(List(1,2,3,-4,5) exists (_ < 0))    // true


