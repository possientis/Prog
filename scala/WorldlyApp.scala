// A singleton object with a main method that allows
// this singleton object to be run as an application.
// This file can't be run from a script, because it
// ends in a definition. It must be compiled.
object WorldlyApp {
  def main(args: Array[String]) {
    val wg = new WorldlyGreeter("Hello")
    wg.greet()
  }
}
