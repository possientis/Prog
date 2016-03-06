// equality in scala:
// == is usual equality for value types (subclassing AnyVal)
// == cannot be overriden and is an alias of equals which can be overriden
// for reference types (subclassing AnyRef). equals is by default implemented
// as reference identity.
// there is the method 'eq' which cannot be overriden and always refer to
// reference identity for reference types

def isEqual1(x: Int, y: Int) = x == y
def isEqual2(x: Any, y: Any) = x == y

println(isEqual1(42,42))
println(isEqual2(42,42))


