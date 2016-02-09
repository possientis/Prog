// The WorldlyGreeter class

class WorldlyGreeter(greeting: String) {
  def greet() {
    val worldlyGreeting = WorldlyGreeter.worldify(greeting)
    println(worldlyGreeting)
  }
}

// The WorldlyGreeter companion object
object WorldlyGreeter {
  def worldify(s: String) = s + ", world!"
}


