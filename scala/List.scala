val diag = List(List(1,0,0), List(0,1,0), List(0,0,1))
val test = List(List(1,2),List(4,5,3,2))

val empty : List[Nothing] = List()


// the list type in scala is covariant: if S <= T then List[S] <= List[T]
// where <= is the subtype relation

// the empty list List() has type List[Nothing] which is a subtype of any List[T]
// since Nothing is the bottom type.

println(Nil == List())  // true

// the 'cons' operator is '::' (which is associative to the right)
// any operator ending with a colon ':' is scala is right associative

println(Nil.isEmpty)  // true

println((5::7::Nil).head) // 5
println((5::7::Nil).tail) // List(7)


// insertion sort
def isort(xs: List[Int]): List[Int] =
  if(xs.isEmpty) Nil
  else insert(xs.head, isort(xs.tail))

def isort2(xs: List[Int]): List[Int] = xs match {
  case Nil    => Nil
  case y::ys  => insert2(y, isort2(ys))
}



def insert(x:Int, xs: List[Int]): List[Int] = 
  if(xs.isEmpty || x <= xs.head) x::xs
  else xs.head :: insert(x, xs.tail)

def insert2(x: Int, xs: List[Int]): List[Int] = xs match {
  case Nil    => x::Nil
  case y::ys  => if (x <= y) x::xs else y::insert2(x, ys)
} 

println(isort(List(8,4,0,2,4,1,7)))   // List(0,1,2,4,4,7,8)
println(isort2(List(8,4,0,2,4,1,7)))  // List(0,1,2,4,4,7,8)

// list pattern matching, variable binding
val List(a,b,c) = List(4,5,6)
println(a)  // 4
println(b)  // 5 
println(c)  // 6

val d::e::rest = List(4,5,6,7,8)
println(d)  // 4
println(e)  // 5
