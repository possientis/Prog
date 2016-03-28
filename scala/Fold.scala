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
