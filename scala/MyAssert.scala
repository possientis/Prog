// assert, making assertion
var assertionsEnabled = true

def myAssert(predicate: () => Boolean) =
  if (assertionsEnabled && !predicate())
    throw new AssertionError

myAssert(() => (5 > 3))

// by-name argument , call by name (argument not evaluated when passed to method)
def byNameAssert(predicate: => Boolean) =
  if (assertionsEnabled && !predicate)
    throw new AssertionError

byNameAssert(5 > 3) // better syntax than before

def boolAssert(predicate: Boolean) =
  if (assertionsEnabled & !predicate)
    throw new AssertionError

boolAssert(5 > 3) // this works too with good syntax however ...
// expression being testing will always be evaluated even when
// assertions are disabled

assertionsEnabled = false
boolAssert(false)
// any side effect in expression will take place even if assertions disabled
try {
  boolAssert(throw new Exception) // exception thrown despite assertions disabled
} catch {
  case e: Exception => println("Exception was caught") // try catch exception
}

byNameAssert(throw new Exception)
println("No exception is thrown in this case")
// more generally, no side effect from expression being tested when
// assertions are disabled

