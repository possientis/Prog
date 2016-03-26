// append is ::: , however let's play

def append[T](xs: List[T], ys: List[T]): List[T] = xs match {
  case Nil    => ys
  case z::zs  => z::append(zs,ys)
}

val l1 = List(5,2,7)
val l2 = List(9,2,3)
val l3 = List(3,4,6,2,9,0)

println(append(l1,l2))  // List(5,2,7,9,2,3)

println(l1.isEmpty)     // false
println(l2.isEmpty)     // false
println(Nil.isEmpty)    // true

println(l1.length == 0) // very bad way to test whether empty list
// O(1)
println(l1.head)        // 5
println(l1.tail)        // List(2,7)

// O(n)
println(l1.last)        // 7 , last element of a list
println(l1.init)        // List(5,2), initial segment 


println(l1.reverse)     // List(7,2,5)

println(l1.reverse.init)
println(l1.tail)

def rev[T](xs: List[T]): List[T] = xs match {
  case Nil  => Nil
  case x :: xs1 => rev(xs1) ::: List(x) // O(n^2), very bad complexity
}

println(l3 take 4)      // List(3,4,6,2)
println(l3 drop 2)      // List(6,2,9,0)

println(l3 splitAt 2)           // (List(3,4),List(6,2,9,0))
println((l3 take 2, l3 drop 2)) // idem, but splitAt quicker

// random access, inefficient
println(l3(4))            // 9, index 4, 5th element
println(l3 apply 4)       // 9
println((l3 drop 4).head) // 9 
println(l3.indices)       // Range(0,1,2,3,4,5)

println(l3.indices.isInstanceOf[Range])     // true

println(l3.indices zip l3)// Vector((0,3), (1,4), (2,6), (3,2), (4,9), (5,0))

println(l1 zip l2)        // List((5,9), (2,2), (7,3))

println(l3.zipWithIndex)  // List((3,0), (4,1), (6,2), (2,3), (9,4), (0,5)) , zip with index

println(l3.toString)      // List(3, 4, 6, 2, 9, 0)

println(l3.mkString("[",", ","]"))  // [3, 4, 6, 2, 9, 0] python, haskell
println(l3.mkString("("," ",")"))   // (3 4 6 2 9 0) scheme 

println(l3 mkString " ")            // 3 4 6 2 9 0
println(l3 mkString "")             // 346290


// using a string builder
val buf = new StringBuilder
println(l3 addString (buf, "(", ";", ")")) // (3;4;6;2;9;0)

// conversion from list to array and vice versa
val arr = l3.toArray
val arr2 = Array(3,4,6,2,9,0)
println(arr2) // [I@69e1968d , ??????

println(arr.toList) // List(3, 4, 6, 2, 9, 0)

val arr3 = new Array[Int](10)
println(arr3) // [I@5ceeb4a3 -- wtf

List(1,2,3) copyToArray (arr2,3)

println(arr2(3))  // 1
println(arr2(4))  // 2 
println(arr2(5))  // 3

// extracting an iterator from a list

val it = l3.iterator
val it2 = arr.iterator
println(it)   // non-empty iterator
println(it2)  // non-empty iterator




 


