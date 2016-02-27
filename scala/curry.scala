def curriedSum(x: Int)(y: Int) = x + y  // curry type definition 

println(curriedSum(3)(5))

val onePlus = curriedSum(1)_  // the '_' is required here (bit of a shame)

println(onePlus(6))


def twice(op: Double => Double, x: Double) = op(op(x))

println(twice(_+1, 5))
