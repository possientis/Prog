// lambda expression
val func1 = (x: Int) => x + 1
println(func1(10))

val func2 : (Int => Int) = (x: Int) => x + 2
println(func2(10))

val func3 = (x:Int) => {
  println("Line 1.")
  println("Line 2.")
  x + 10
}
println(func3(10))


val someNumbers = List(-11, -10, -5, 0, 5, 10)
someNumbers.foreach((x:Int) => println(x))
someNumbers.foreach(println _)
someNumbers.foreach(println)  // succeeds, compiler expecting a function


println(someNumbers.filter((x) => x > 0))
println(someNumbers.filter(x => x > 0))
println(someNumbers.filter(_ > 0))

val f = (_:Int) + (_:Int) // f takes two parameters, not one
println(f(5,10))

val g = (_:Int) => (_:Int) + (_:Int) // g takes a single parameter ...
println(g(5656)(5,10))  // ... but is not what we think it is

val h = (x:Int) => x + x
println(h(5))


def sum(a:Int, b:Int, c:Int) = a + b + c
val k = sum _  // k = sum
//val k2 = sum  // fails, compiler not expecting a function
println(k(2,3,4))

def H(d : (Int, Int, Int) => Int) = d
println(H(k)(3,4,5))
println(H(sum)(3,4,5))
println(H(sum _)(3,4,5))

val l = sum(3, _:Int, 4)
println(l(10))

var total = 0
someNumbers.foreach(total += _)   // captured variable is reference
println(total)




