// assert(condition) and assert(condition, message)
// will throw an AssertionError. You may wish to use
// assume(condition) and assume(condition, message)
// which will throw an IllegalArgumentException.


// command lines options -ea and -da to enable and disable assertions. 


// this is the theory ...

// in practice, seems like assume also throws AssertionError ...

def inverse(x: Double) = { assume(x != 0, "must be non-zero"); 1/x }

println(inverse(2))
