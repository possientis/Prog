def msort[T] (less: (T, T) => Boolean) (xs: List[T]): List[T] = { // currying in play
  def merge(xs: List[T], ys: List[T]): List[T] = (xs, ys) match {
    case (Nil, _)   => ys
    case (_, Nil)   => xs
    case (x :: xs1, y :: ys1) =>
      if (less(x, y)) x :: merge(xs1, ys) else y :: merge(xs, ys1)
  }
  val n = xs.length/2
  if (n == 0) xs
  else {
    val (ys, zs) = xs splitAt n
    merge(msort(less)(ys), msort(less)(zs))
  }
}


val l = List(3,7,1,0,9,8,5,4,2,1,7,5)

println(msort[Int](_<=_)(l))  // List(0, 1, 1, 2, 3, 4, 5, 5, 7, 7, 8, 9)  
println(msort((x:Int, y:Int) => x<=y)(l))
println(msort[Int](_>=_)(l)) // List(9, 8, 7, 7, 5, 5, 4, 3, 2, 1, 1, 0)  
println(msort[Int](_<_)(l))  // List(0, 1, 1, 2, 3, 4, 5, 5, 7, 7, 8, 9)  

val intSort = msort[Int](_<_) _
println(intSort(l))          // List(0, 1, 1, 2, 3, 4, 5, 5, 7, 7, 8, 9)  

