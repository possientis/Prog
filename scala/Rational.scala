class Rational(n: Int, d: Int) {

  // each instance of rational carries this code?
  private def gcd(a: Int, b: Int): Int =
    if (b == 0) a else gcd(b, a % b)

  private val g = gcd(n, d)
  val numer: Int = n / g
  val denom: Int = d / g

  def this(n: Int) = this(n,1)
  // addition
  def +(that: Rational): Rational =
    new Rational(numer * that.denom + that.numer * denom, 
                 denom * that.denom)
  // subtraction
  def -(that: Rational): Rational =
    new Rational(numer * that.denom - that.numer * denom, 
                 denom * that.denom)
  // multiplication
  def *(that: Rational): Rational =
    new Rational(numer * that.numer, denom * that.denom)
  
  // division
  def /(that: Rational): Rational =
    new Rational(numer * that.denom, denom * that.numer)

  override def toString() = numer+"/"+denom

  def <(that: Rational) = 
    this.numer * that.denom < that.numer * this.denom // wrong mathematically

  def +(that: Int): Rational = {println("Int overload running"); this + new Rational(that)}
  def -(that: Int): Rational = this - new Rational(that)
  def *(that: Int): Rational = this * new Rational(that)
  def /(that: Int): Rational = this / new Rational(that)

}


implicit def intToRational(x: Int) = { println("implicit conversion from Int to Rational"); new Rational(x)} 

val x = new Rational(3,4)
val y = new Rational(4,10)
println("x = " + x)
println("y = " + y)
println("x + y = " + (x + y))
println("x - y = " + (x - y))
println("x * y = " + (x * y))
println("x / y = " + (x / y))
println("x < y = " + (x < y))
println("x + 3 = " + (x + 3))
println("3 + x = " + (3 + x))

