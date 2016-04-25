import scala.collection.mutable.ListBuffer


val buf = new ListBuffer[Int]

val xs = List(1,2,3,4,5)

for(x <- xs) buf += x + 1   // += constant time (append)

// toList is also constant time
println(buf.toList) // List(2, 3, 4, 5, 6)


trait MyList[+T]{
  def myMap[U](f: T=> U): List[U] = {
    val b = new ListBuffer[U]
    var cdr = this
    while(!cdr.isEmpty){
      b += f(cdr.head)
      cdr = cdr.tail
    }
  }
  b.toList
}


