class CarefulGreeter(greeting: String) {
  if (greeting == null)
  throw new NullPointerException("greeting was null")
  def greet() = println(greeting)
}

// will throw exception
val g = new CarefulGreeter(null)
