class RepeatGreeter(greeting: String, count: Int) {
  // auxiliary constructor calling primary constructor
  def this(greeting: String) = this(greeting, 1)
  def greet() = {
  for (i <- 1 to count)
  println(greeting)
  }
}

val g1 = new RepeatGreeter("Hello, world", 3)
g1.greet()

val g2 = new RepeatGreeter("Hi there!")
g2.greet()

