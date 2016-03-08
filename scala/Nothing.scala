// Nothing is at the bottom of the type hierarchy and has not value
def error(message: String): Nothing = throw new Error(message)

def divide(x: Int, y: Int): Int =
  if (y != 0) x / y
  // Nothing is a subtype of Int, so all good
  else error("can't divide by zero")



