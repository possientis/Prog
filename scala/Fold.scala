// folding lists (fold, Fold) 

def sum(xs: List[Int]): Int = (0 /: xs) (_ + _) // fold left '/:' (think of syntax tree '/')

println(sum(List(1,2,3,4,5))) // 15

def product(xs: List[Int]): Int = (1 /: xs) (_ * _) // fold left '/:'
  
println(product(List(1,2,3,4,5))) // 120

val words = List("the", "quick", "brown", "fox")

println(("" /: words) (_ + " " + _))                // ' the quick brown fox' fold left '/:'

println((words.head /: words.tail) (_ + " " + _ ))  // 'the quick brown fox'  fold left '/:'


def flatten1[T](xss: List[List[T]]) = 
  (List[T]() /: xss) (_ ::: _)        // flatten with fold left '/:'

def flatten2[T](xss: List[List[T]]) = 
  (xss :\ List[T]()) (_ ::: _)        // flatten with fold right ':\'

// concatenation xs ::: ys takes time proportional to length of xs (first argument)
// the implementation of flatten in terms of fold right is more efficient

// linear 'reverse' using fold left
def reverse2[T](xs: List[T]) = (List[T]() /: xs) ((acc,x) => x::acc)

println(reverse2(List(1,2,3,4,5,6,7))) // List(7, 6, 5, 4, 3, 2, 1)


def reverse3[T](xs: List[T]) = (List[T]() /: xs) {(acc,x) => x::acc} // curly brace works too


// sort
println(List(1, -3, 4, 2, 6) sortWith (_ < _))


println(List.apply(1,2,3))  // List(1,2,3) apply
println(List.range(1,5))    // List(1, 2, 3, 4)  range
println(List.range(9,1,-3)) // List(9, 6, 3)  range
println(List.make(5,'a'))   // List(a, a, a, a, a) make (deprecated use 'fill')

val zipped = "abcde".toList zip List(1,2,3)
println(zipped)             // List((a,1), (b,2), (c,3)) zip
println(zipped.unzip)       // (List(a, b, c),List(1, 2, 3))

val xss = List(List('a','b'), List('c'), List('d', 'e'))
println(xss.flatten)        // List(a, b, c, d, e)
println(List.concat(List('a','b'), List('c'), List('d', 'e'))) // List(a, b, c, d, e)




