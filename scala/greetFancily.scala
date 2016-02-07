// no var no val qualification of 'greeting here'
// => 'greeting' is a private member of class
// try adding 'val' or 'var' and field becomes
// public.
class FancyGreeter(greeting: String) {
  def greet() = println(greeting)
  // will fail
  def foo() = {//greeting = "new value"}
}

val g = new FancyGreeter("Salutations, world")
g.greet()

// will fail, greeting private
//println(g.greeting)
